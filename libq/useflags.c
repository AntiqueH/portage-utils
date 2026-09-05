/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.        - <antiq.hofer@gmail.com>
 *
 * USE/IUSE evaluation against the configuration, factored out of
 * qmerge so it can be fuzzed. USE and IUSE strings it
 * consumes are read verbatim from a remote Packages index and are
 * therefore untrusted. Config state is passed in via struct use_ctx now.
 * Yes, we like fuzz this much.
 */

#include "main.h"

#include <ctype.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "atom.h"
#include "array.h"
#include "colors.h"
#include "set.h"
#include "tree.h"
#include "xalloc.h"
#include "xasprintf.h"
#include "useflags.h"

static bool uc_probe_warned = false;

static set *
uc_flags_to_set(const char *str)
{
	set  *s = create_set();
	char *tmp;
	char *tok;
	char *sp;

	if (str == NULL)
		return s;
	tmp = xstrdup(str);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok != '\0')
			add_set_unique(tok, s, NULL);
	}
	free(tmp);
	return s;
}

static void
uc_expand_pfxs_add(array *into, const char *grps)
{
	char *tmp;
	char *tok;
	char *sp;

	if (grps == NULL || *grps == '\0')
		return;
	tmp = xstrdup(grps);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		struct use_expand_pfx *ep = xmalloc(sizeof(*ep));
		size_t                 i;

		ep->var = xstrdup(tok);
		xasprintf(&ep->pfx, "%s_", tok);
		for (i = 0; ep->pfx[i] != '\0'; i++)
			ep->pfx[i] = (char)tolower((unsigned char)ep->pfx[i]);
		array_append(into, ep);
	}
	free(tmp);
}

void
use_ctx_free(struct use_ctx *uc)
{
	if (uc->expand_pfxs != NULL) {
		size_t                 i;
		struct use_expand_pfx *ep;

		array_for_each(uc->expand_pfxs, i, ep) {
			free(ep->pfx);
			free(ep->var);
			free(ep);
		}
		array_free(uc->expand_pfxs);
		uc->expand_pfxs = NULL;
	}
	if (uc->hidden != NULL) {
		free_set(uc->hidden);
		uc->hidden = NULL;
	}
}

const struct use_expand_pfx *
uc_expand_group(struct use_ctx *uc, const char *tok, const char **suffix)
{
	const struct use_expand_pfx *best = NULL;
	struct use_expand_pfx       *ep;
	size_t                       blen = 0;
	size_t                       i;

	if (uc->expand_pfxs == NULL) {
		uc->expand_pfxs = array_new();
		uc_expand_pfxs_add(uc->expand_pfxs, uc->use_expand);
		uc_expand_pfxs_add(uc->expand_pfxs, uc->use_expand_implicit);
	}
	array_for_each(uc->expand_pfxs, i, ep) {
		size_t l = strlen(ep->pfx);

		if (l > blen && strncmp(tok, ep->pfx, l) == 0) {
			best = ep;
			blen = l;
		}
	}
	if (best != NULL && suffix != NULL)
		*suffix = tok + blen;
	return best;
}

bool
uc_expand_group_hidden(struct use_ctx *uc, const char *var)
{
	if (uc->hidden == NULL) {
		char *tmp;
		char *tok;
		char *sp;

		uc->hidden = create_set();
		if (uc->use_expand_hidden != NULL) {
			bool ign;

			tmp = xstrdup(uc->use_expand_hidden);
			for (tok = strtok_r(tmp, " \t\n", &sp);
				 tok != NULL;
				 tok = strtok_r(NULL, " \t\n", &sp))
			{
				/* strincr_var keeps -TOK negations verbatim; honor
				 * them here (profiles unhide e.g. ABI_X86 that way) */
				if (tok[0] == '-')
					del_set(tok + 1, uc->hidden, &ign);
				else
					uc->hidden = add_set_unique(tok, uc->hidden, NULL);
			}
			free(tmp);
		}
	}
	return contains_set(var, uc->hidden) != NULL;
}

int
uc_pkg_flag_override(depend_atom *pa, const char *tok, array *lst)
{
	pkgcfg_t *pc;
	size_t    i;
	int       r = -1;

	if (lst == NULL)
		return -1;
	array_for_each(lst, i, pc) {
		char *tmp;
		char *t;
		char *sp;

		if (atom_compare(pa, pc->atom) != EQUAL)
			continue;
		tmp = xstrdup(pc->vals);
		for (t = strtok_r(tmp, " \t", &sp);
			 t != NULL;
			 t = strtok_r(NULL, " \t", &sp))
		{
			if (t[0] == '-') {
				if (strcmp(t + 1, tok) == 0)
					r = 0;
			} else if (strcmp(t, tok) == 0) {
				r = 1;
			}
		}
		free(tmp);
	}
	return r;
}

/* raw config variable lookup (make.globals/profiles/make.conf) */
static const char *
uc_config_var(struct use_ctx *uc, const char *name)
{
	const char *v = NULL;

	if (uc->all_config_vars != NULL)
		v = get_set(name, uc->all_config_vars);
	if (v == NULL)
		v = getenv(name);
	return v;
}

bool
uc_use_wanted(struct use_ctx *uc, depend_atom *pa, const char *tok,
			  bool def_on)
{
	const struct use_expand_pfx *ep;
	const char                  *sfx  = NULL;
	bool                         want = def_on;
	int                          o;

	ep = uc_expand_group(uc, tok, &sfx);
	if (ep != NULL) {
		const char *v = uc_config_var(uc, ep->var);

		if (v != NULL) {
			char *tmp = xstrdup(v);
			char *t;
			char *sp;

			want = false;
			for (t = strtok_r(tmp, " \t\n", &sp);
				 t != NULL;
				 t = strtok_r(NULL, " \t\n", &sp))
				if (strcmp(t, sfx) == 0)
					want = true;
			free(tmp);
		}
	} else if (strchr(tok, '_') != NULL) {
		const char *us = strrchr(tok, '_');

		while (us != NULL && us > tok) {
			char        var[128];
			size_t      plen = (size_t)(us - tok);
			const char *v;
			size_t      i;

			if (plen >= sizeof(var))
				break;
			for (i = 0; i < plen; i++)
				var[i] = (char)toupper((unsigned char)tok[i]);
			var[plen] = '\0';
			v = uc_config_var(uc, var);
			if (v != NULL) {
				char *tmp = xstrdup(v);
				char *t;
				char *sp;

				if (!uc_probe_warned) {
					uc_probe_warned = true;
					warn("USE_EXPAND does not declare a group for "
						 "'%s': resolving it from the config "
						 "variable %s (no profile?)", tok, var);
				}
				want = false;
				for (t = strtok_r(tmp, " \t\n", &sp);
					 t != NULL;
					 t = strtok_r(NULL, " \t\n", &sp))
					if (strcmp(t, us + 1) == 0)
						want = true;
				free(tmp);
				break;
			}
			do {
				us--;
			} while (us > tok && *us != '_');
			if (us <= tok || *us != '_')
				break;
		}
	}
	if (uc->ev_use_neg != NULL &&
			(contains_set(tok, uc->ev_use_neg) != NULL ||
			 contains_set("*", uc->ev_use_neg) != NULL))
		want = false;
	if (uc->ev_use != NULL && contains_set(tok, uc->ev_use) != NULL)
		want = true;
	o = uc_pkg_flag_override(pa, tok, uc->pkg_use);
	if (o != -1)
		want = o == 1;
	o = uc_pkg_flag_override(pa, tok, uc->pkg_use_force);
	if (o == 1 || (o == -1 && uc->use_force != NULL &&
			contains_set(tok, uc->use_force) != NULL))
		want = true;
	o = uc_pkg_flag_override(pa, tok, uc->pkg_use_mask);
	if (o == 1 || (o == -1 && uc->use_mask != NULL &&
			contains_set(tok, uc->use_mask) != NULL))
		want = false;
	return want;
}

int
uc_use_mismatch(struct use_ctx *uc, tree_pkg_ctx *pkg)
{
	char        *iusestr = tree_pkg_meta(pkg, Q_IUSE);
	depend_atom *pa;
	set         *bu;
	char        *tmp;
	char        *tok;
	char        *sp;
	int          mis = 0;

	if (iusestr == NULL || *iusestr == '\0')
		return 0;
	pa  = tree_pkg_atom(pkg, true);
	bu  = uc_flags_to_set(tree_pkg_meta(pkg, Q_USE));
	tmp = xstrdup(iusestr);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		bool def_on = tok[0] == '+';
		bool on;

		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok == '\0')
			continue;
		on = contains_set(tok, bu) != NULL;
		if (on != uc_use_wanted(uc, pa, tok, def_on))
			mis++;
	}
	free(tmp);
	free_set(bu);
	return mis;
}

char *
uc_use_drift(tree_pkg_ctx *bpkg, tree_pkg_ctx *ipkg)
{
	char  *iusestr = tree_pkg_meta(bpkg, Q_IUSE);
	set   *bu;
	set   *iu;
	set   *oldiuse;
	char  *tmp;
	char  *tok;
	char  *sp;
	char   out[2048] = "";
	size_t olen = 0;

	if (iusestr == NULL || *iusestr == '\0')
		return NULL;

	bu      = uc_flags_to_set(tree_pkg_meta(bpkg, Q_USE));
	iu      = uc_flags_to_set(tree_pkg_meta(ipkg, Q_USE));
	oldiuse = uc_flags_to_set(tree_pkg_meta(ipkg, Q_IUSE));
	tmp = xstrdup(iusestr);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		bool b;
		bool iv;
		bool known;

		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok == '\0')
			continue;

		b  = contains_set(tok, bu) != NULL;
		iv = contains_set(tok, iu) != NULL;
		if (b == iv)
			continue;
		known = contains_set(tok, oldiuse) != NULL;
		if (olen + strlen(tok) + 24 >= sizeof(out))
			break;
		/* emerge colour semantics (output_helpers._create_use_string):
		 * a TOGGLED flag is green with a "*" marker; a flag the
		 * installed copy did not even know (new in IUSE) is yellow
		 * with "%".  Red/blue mean unchanged and never apply here. */
		olen += (size_t)snprintf(out + olen, sizeof(out) - olen,
								 "%s%s%c%s%s%s", olen > 0 ? " " : "",
								 *NORM == '\0' ? "" :
								 known ? "\033[32;01m" : "\033[33;01m",
								 b ? '+' : '-', tok, NORM,
								 known ? "*" : b ? "%*" : "%");
	}
	free(tmp);
	free_set(bu);
	free_set(iu);
	free_set(oldiuse);

	return olen > 0 ? xstrdup(out) : NULL;
}