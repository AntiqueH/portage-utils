/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2005-2008 Ned Ludd        - <solar@gentoo.org>
 * Copyright 2005-2014 Mike Frysinger  - <vapier@gentoo.org>
 * Copyright 2018-     Fabian Groffen  - <grobian@gentoo.org>
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 */

#include "main.h"
#include "applets.h"

#include <xalloc.h>
#include <assert.h>
#include <ctype.h>
#include <sys/time.h>
#include <limits.h>
#include <termios.h>
#include <sys/ioctl.h>

#include "eat_file.h"
#include "rmspace.h"
#include "scandirat.h"
#include "atom.h"
#include "set.h"
#include "xasprintf.h"

/* variables to control runtime behavior */
char *main_overlay;
char *module_name = NULL;
int verbose = 0;
int quiet = 0;
int twidth;
bool nocolor;
bool qmerge_nocolor;
char *qmerge_jobs_conf;
bool qmerge_prefetch;
char *qmerge_moves_conf;
char *qmerge_local_priority_conf;
char *qmerge_lenient_conf;
char *qmerge_keep_going_conf;
char *qmerge_respect_use_conf;
char *qmerge_rebuilt_conf;
bool qnews_enable;
bool qmerge_blockers;
char *qetuto_keyservers_conf;
char *qetuto_keys_conf;
char *qetuto_external_refresh_conf;
char *binpkg_gpg_verify_gpg_home;
char *binpkg_tar_opts;
char *accept_chosts;
char *binpkg_gpg_signing_base_command;
char *binpkg_gpg_signing_digest;
char *binpkg_gpg_signing_gpg_home;
char *binpkg_gpg_signing_key;
char pretend = 0;
char *portarch;
char *portroot;
char *configroot;
char *config_protect;
char *config_protect_mask;
char *collision_ignore;
char *portvdb;
char *portlogdir;
char *pkg_install_mask;
char *binhost;
char *qfetchcommand;
char *qresumecommand;
char *qfetchwrapper;
char *fetchwrapper;
char *chost;
char *cbuild;
char *accept_keywords;
char *accept_properties;
char *accept_restrict;
char *gentoo_mirrors;
char *iuse_implicit;
char *use_expand;
char *use_expand_hidden;
char *use_expand_implicit;
char *use_expand_unprefixed;
char *var_elibc;
char *var_kernel;

/* every VAR=value seen in make.globals/profiles/make.conf, raw,
 * last-wins; used e.g. to resolve USE_EXPAND member variables */
set *all_config_vars = NULL;
/* profile-stacked use.mask/use.force (incl. stable variants) */
set *use_mask  = NULL;
set *use_force = NULL;
/* stacked package.accept_keywords/package.keywords entries */
array *pkg_accept_keywords = NULL;
array *pkg_license = NULL;
array *pkg_use = NULL;
array *pkg_use_force = NULL;
array *pkg_use_mask = NULL;
/* license group name -> space-joined members (GLEP 23), merged across
 * all overlays' profiles/license_groups */
set *license_groups = NULL;
char *pkgdir;
char *port_tmpdir;
set  *features;
set  *ev_use;
set  *ev_use_neg;
char *install_mask;
char *binpkg_format;
char *binpkg_compress;
char *binpkg_compress_flags;
char *qgtree_compress;
array *overlays;
array *overlay_names;
array *overlay_src;

char *portedb;
static char *eprefix;
char *accept_license;

#define STR_DEFAULT "built-in default"

/* helper functions for showing errors */
const char *argv0;

FILE *warnout;

#ifdef EBUG
# include <sys/resource.h>
static void
init_coredumps(void)
{
	struct rlimit rl;
	rl.rlim_cur = RLIM_INFINITY;
	rl.rlim_max = RLIM_INFINITY;
	setrlimit(RLIMIT_CORE, &rl);
}
#endif

static void
setup_quiet(void)
{
	/* "e" for FD_CLOEXEC */
	if (quiet == 0)
		warnout = fopen("/dev/null", "we");
	++quiet;
}

/* display usage and exit */
void
usage(int status, const char *flags, struct option const opts[],
      const char * const help[], const char *desc, int blabber)
{
	const char opt_arg[] = "[arg]";
	const char a_arg[] = "<arg>";
	size_t a_arg_len = strlen(a_arg) + 1;
	size_t i;
	size_t optlen;
	size_t l;
	size_t prefixlen;
	const char *hstr;
	FILE *fp = status == EXIT_SUCCESS ? stdout : warnout;

	if (blabber == 0) {
		fprintf(fp, "%susage:%s %sq%s %s<applet> <args>%s  : %s"
			"invoke a portage utility applet\n\n", GREEN,
			NORM, YELLOW, NORM, DKBLUE, RED, NORM);
		fprintf(fp, "%scurrently defined applets:%s\n", GREEN, NORM);
		for (i = 0; applets[i].desc; ++i)
			if (applets[i].func)
				fprintf(fp, " %s%9s%s %s%-16s%s%s:%s %s\n",
					YELLOW, applets[i].name, NORM,
					DKBLUE, applets[i].opts, NORM,
					RED, NORM, applets[i].desc);
	} else if (blabber > 0) {
		fprintf(fp, "%susage:%s %s%s%s [opts] %s%s%s %s:%s %s\n",
			GREEN, NORM,
			YELLOW, applets[blabber].name, NORM,
			DKBLUE, applets[blabber].opts, NORM,
			RED, NORM, applets[blabber].desc);
		if (desc)
			fprintf(fp, "\n%s\n", desc);
	}
	if (module_name != NULL)
		fprintf(fp, "%sloaded module:%s\n%s%8s%s %s<args>%s\n",
			GREEN, NORM, YELLOW, module_name, NORM, DKBLUE, NORM);

	/* Prescan the --long opt length to auto-align. */
	optlen = 0;
	for (i = 0; opts[i].name; ++i) {
		l = strlen(opts[i].name);
		if (opts[i].has_arg != no_argument)
			l += a_arg_len;
		optlen = MAX(l, optlen);
	}

	fprintf(fp, "\n%soptions:%s -[%s]\n", GREEN, NORM, flags);
	for (i = 0; opts[i].name; ++i) {
		/* this assert is a life saver when adding new applets. */
		assert(help[i] != NULL);

		/* first output the short flag if it has one */
		if (opts[i].val > '~' || opts[i].val < ' ')
			fprintf(fp, "      ");
		else
			fprintf(fp, "  -%c, ", opts[i].val);

		/* then the long flag */
		if (opts[i].has_arg == no_argument)
			fprintf(fp, "--%-*s %s*%s ", (int)optlen, opts[i].name,
				RED, NORM);
		else
			fprintf(fp, "--%s %s%s%s%*s %s*%s ",
				opts[i].name,
				DKBLUE, (opts[i].has_arg == a_argument ? a_arg : opt_arg), NORM,
				(int)(optlen - strlen(opts[i].name) - a_arg_len), "",
				RED, NORM);

		/* then wrap the help text, if necessary */
		prefixlen = 6 + 2 + optlen + 1 + 1 + 1;
		if ((size_t)twidth < prefixlen + 10) {
			fprintf(fp, "%s\n", help[i]);
		} else {
			const char *t;
			hstr = help[i];
			l = strlen(hstr);
			while (twidth - prefixlen < l) {
				/* search backwards for a space */
				t = &hstr[twidth - prefixlen];
				while (t > hstr && !isspace((int)*t))
					t--;
				if (t == hstr)
					break;
				fprintf(fp, "%.*s\n%*s",
						(int)(t - hstr), hstr, (int)prefixlen, "");
				l -= t + 1 - hstr;
				hstr = t + 1;  /* skip space */
			}
			fprintf(fp, "%s\n", hstr);
		}
	}
	exit(status);
}

void
version_barf(void)
{
	const char *vcsid = "";
	const char *eprefixid = "";

#ifndef VERSION
# define VERSION "git"
#endif

#ifdef VCSID
	vcsid = " (" VCSID ")";
#endif

	if (strlen(CONFIG_EPREFIX) > 1)
		eprefixid = "configured for " CONFIG_EPREFIX "\n";

	printf("portage-utils-%s%s\n"
	       "%s"
	       "written for Gentoo by solar, vapier and grobian\n",
	       VERSION, vcsid, eprefixid);
	exit(EXIT_SUCCESS);
}

void
freeargv(int argc, char **argv)
{
	while (argc--)
		free(argv[argc]);
	free(argv);
}

void
makeargv(const char *string, int *argc, char ***argv)
{
	int curc = 2;
	char *q, *p, *str;
	(*argv) = xmalloc(sizeof(char *) * curc);

	*argc = 1;
	(*argv)[0] = xstrdup(argv0);

	/* shortcut empty strings */
	while (isspace((int)*string))
		string++;
	if (*string == '\0')
		return;

	q = xstrdup(string);
	str = q;

	remove_extra_space(str);
	rmspace(str);

	while (str) {
		if ((p = strchr(str, ' ')) != NULL)
			*(p++) = '\0';

		if (*argc == curc) {
			curc *= 2;
			(*argv) = xrealloc(*argv, sizeof(char *) * curc);
		}
		(*argv)[*argc] = xstrdup(str);
		(*argc)++;
		str = p;
	}
	free(q);
}

static void
strincr_var(const char *name, const char *s, char **value, size_t *value_len)
{
	size_t len;
	char  *p;
	char  *nv;
	char   brace;
	bool   haddashstar;

	/* find/skip any -* instances */
	nv = q_deconst(s);
	while ((p = strstr(nv, "-*")) != NULL)
		nv = p + 2;

	haddashstar = nv != s;

	len = strlen(nv);
	if (haddashstar && len < *value_len) {
		p = *value;
		*p = '\0';  /* in case len == 0 */
	} else if (haddashstar) {
		p = *value = xrealloc(*value, len + 1);
	} else {
		*value = xrealloc(*value, *value_len + 1 + len + 1);
		p = &(*value)[*value_len];
		if (*value_len > 0)
			*p++ = ' ';
	}
	memcpy(p, nv, len + 1);

	/* This function is mainly used by the startup code for parsing
		make.conf and stacking variables remove.
		variables can be in the form of ${v} or $v
		works:
			FEATURES="${FEATURES} foo"
			FEATURES="$FEATURES foo"
			FEATURES="baz bar -* foo"

		wont work:
			FEATURES="${OTHERVAR} foo"
			FEATURES="-nls nls -nls"
			FEATURES="nls nls nls"
	*/

	len = strlen(name);
	while ((p = strchr(p, '$')) != NULL) {
		nv = p;
		p++;  /* skip $ */
		brace = *p == '{';
		if (brace)
			p++;
		if (strncmp(p, name, len) == 0) {
			p += len;
			if (brace && *p == '}') {
				p++;
				memset(nv, ' ', p - nv);
			} else if (!brace && (*p == '\0' || isspace((int)*p))) {
				memset(nv, ' ', p - nv);
			}
		}
	}

	remove_extra_space(*value);
	*value_len = strlen(*value);
	/* we should sort here */
}

/* this neg when given records explicit "-flag" negations (and "-*" as the
 * literal "*") */
static void
setincr_var(const char *s, set **vals, set **neg)
{
	int    i;
	int    argc;
	char **argv;
	bool   ignore;

	/* This tries to mimick parsing of portage envvars and the stacking
	 * thereof.  In particular USE and FEATURES, where also negation can
	 * happen (- prefix).  Variables are supported in form of ${v} or
	 * $v, but there's no actual replacement happening, we just ignore
	 * any of such forms.
	 *  works:
	 *		FEATURES="${FEATURES} foo"
	 *		FEATURES="$FEATURES foo"
	 *		FEATURES="baz bar -* foo"
	 *
	 *	wont work:
	 *		FEATURES="${OTHERVAR} foo"
	 *		FEATURES="-* ${FEATURES}"
	 */

	if (s == NULL || *s == '\0')
		return;

	/* break up input */
	makeargv(s, &argc, &argv);

	for (i = 1 /* skip executable name */; i < argc; i++) {
		if (argv[i][0] == '-') {
			if (*vals != NULL) {
				/* handle negation, when the respective value isn't set, we
				 * simply ignore/drop it */
				if (argv[i][1] == '*') {
					clear_set(*vals);
				} else {
					del_set(&argv[i][1], *vals, &ignore);
				}
			}
			if (neg != NULL) {
				if (argv[i][1] == '*') {
					if (*neg != NULL)
						clear_set(*neg);
					*neg = add_set_unique("*", *neg, &ignore);
				} else {
					*neg = add_set_unique(&argv[i][1], *neg, &ignore);
				}
			}
		} else if (argv[i][0] == '$') {
			/* detect ${var} or $var, simply ignore it completely, for
			 * all of these should be stacked, so re-including whatever
			 * there is shouldn't make much sense */
		} else {
			*vals = add_set_unique(argv[i], *vals, &ignore);
			if (neg != NULL && *neg != NULL)
				del_set(argv[i], *neg, &ignore);
		}
	}

	freeargv(argc, argv);
}

static env_vars *
get_portage_env_var(env_vars *vars, const char *name)
{
	size_t i;

	for (i = 0; vars[i].name; ++i)
		if (!strcmp(vars[i].name, name))
			return &vars[i];

	return NULL;
}

static void
set_portage_env_var(env_vars *var, const char *value, const char *src)
{
	switch (var->type) {
	case _Q_BOOL:
		*var->value.b = 0;
		if (strcasecmp(value, "true") == 0 ||
				strcasecmp(value, "yes") == 0 ||
				strcmp(value, "1") == 0)
			*var->value.b = 1;
		free(var->src);
		var->src = xstrdup(src);
		break;
	case _Q_STR:
		free(*var->value.s);
		*var->value.s = xstrdup(value);
		var->value_len = strlen(value);
		free(var->src);
		var->src = xstrdup(src);
		break;
	case _Q_NSTR:
		free(*var->value.s);
		*var->value.s = xstrdup(value);
		remove_extra_space(*var->value.s);
		var->value_len = strlen(*var->value.s);
		free(var->src);
		var->src = xstrdup(src);
		break;
	case _Q_ISTR:
	case _Q_ISET:
		if (strcmp(var->src, STR_DEFAULT) != 0) {
			char *p;

			xasprintf(&p, "%s, %s", var->src, src);
			free(var->src);
			var->src = p;
		} else {
			free(*var->value.s);
			*var->value.s = NULL;
			var->value_len = 0;
			free(var->src);
			var->src = xstrdup(src);
		}
		if (var->type == _Q_ISTR)
			strincr_var(var->name, value, var->value.s, &var->value_len);
		else
			setincr_var(value, var->value.t,
						var->value.t == &ev_use ? &ev_use_neg : NULL);
		break;
	}
}

/* strchr that skips backslash-escaped characters, so quoted values
 * like FETCHCOMMAND="... -U \"Portage\" ..." are scanned correctly */
static char *
strchr_unescaped(char *s, int q)
{
	bool esc = false;

	for (; *s != '\0'; s++) {
		if (esc) {
			esc = false;
			continue;
		}
		if (*s == '\\') {
			esc = true;
			continue;
		}
		if (*s == (char)q)
			return s;
	}
	return NULL;
}

/* stack a profile use.mask/use.force style file (one flag per line,
 * "-flag" reverting a parent entry) into the given set */
static void
read_use_flag_file(const char *file, set **into)
{
	FILE   *fp;
	char   *line = NULL;
	size_t  len  = 0;
	bool    ignore;

	fp = fopen(file, "r");
	if (fp == NULL)
		return;
	while (getline(&line, &len, fp) != -1) {
		char *s = rmspace(line);

		if (*s == '\0' || *s == '#')
			continue;
		if (*s == '-')
			del_set(s + 1, *into, &ignore);
		else
			*into = add_set_unique(s, *into, &ignore);
	}
	free(line);
	fclose(fp);
}

/* fold the global wildcard (star-slash-star) entries of package.use
 * into the USE set; portage treats those as configuration defaults
 * and they are part of the effective USE advertised in the binpkg
 * index header.  Handles the USE_EXPAND shorthand "VAR: val ..." */
static void
read_package_use_global_file(const char *file)
{
	FILE   *fp;
	char   *line = NULL;
	size_t  len  = 0;
	bool    ignore;

	fp = fopen(file, "r");
	if (fp == NULL)
		return;
	while (getline(&line, &len, fp) != -1) {
		char  *s = rmspace(line);
		char  *tok;
		char  *sp;
		char   prefix[128] = "";

		if (*s == '\0' || *s == '#')
			continue;
		tok = strtok_r(s, " \t", &sp);
		if (tok == NULL || strcmp(tok, "*/*") != 0)
			continue;
		while ((tok = strtok_r(NULL, " \t", &sp)) != NULL) {
			size_t tlen = strlen(tok);
			char   flag[256];
			bool   neg;

			if (tlen > 1 && tok[tlen - 1] == ':') {
				size_t pi;

				/* USE_EXPAND shorthand: subsequent flags get the
				 * lowercased variable name as prefix */
				snprintf(prefix, sizeof(prefix), "%.*s_",
						 (int)MIN(tlen - 1, sizeof(prefix) - 2), tok);
				for (pi = 0; prefix[pi] != '\0'; pi++)
					prefix[pi] =
						(char)tolower((unsigned char)prefix[pi]);
				continue;
			}
			neg = tok[0] == '-';
			snprintf(flag, sizeof(flag), "%s%s",
					 prefix, tok + (neg ? 1 : 0));
			if (neg) {
				del_set(flag, ev_use, &ignore);
				ev_use_neg = add_set_unique(flag, ev_use_neg, &ignore);
			} else {
				ev_use = add_set_unique(flag, ev_use, &ignore);
				if (ev_use_neg != NULL)
					del_set(flag, ev_use_neg, &ignore);
			}
		}
	}
	free(line);
	fclose(fp);
}

/* merge every overlay's profiles/license_groups into license_groups;
 * lines are "GROUP member @nested-group ..."; members accumulate */
static void
read_license_groups(void)
{
	size_t  n;
	char   *ov;

	if (overlays == NULL)
		return;
	array_for_each(overlays, n, ov) {
		char    path[_Q_PATH_MAX];
		FILE   *fp;
		char   *line = NULL;
		size_t  len  = 0;

		snprintf(path, sizeof(path), "%s/profiles/license_groups", ov);
		fp = fopen(path, "r");
		if (fp == NULL)
			continue;
		while (getline(&line, &len, fp) != -1) {
			char *s = rmspace(line);
			char *sp;
			char *grp;
			char *members;
			void *prev = NULL;

			if (*s == '\0' || *s == '#')
				continue;
			grp = strtok_r(s, " \t", &sp);
			if (grp == NULL)
				continue;
			members = sp == NULL ? q_deconst("") : rmspace(sp);
			if (license_groups == NULL)
				license_groups = create_set();
			{
				const char *old = get_set(grp, license_groups);
				char       *val;

				if (old != NULL && old[0] != '\0')
					xasprintf(&val, "%s %s", old, members);
				else
					val = xstrdup(members);
				add_set_value(grp, val, &prev, license_groups);
				free(prev);
			}
		}
		free(line);
		fclose(fp);
	}
}

/* load an "atom [values...]" per-line config file (the
 * package.accept_keywords family); invalid atoms are skipped loudly */
static void
read_pkgcfg_file(const char *file, array **into)
{
	FILE   *fp;
	char   *line = NULL;
	size_t  len  = 0;

	fp = fopen(file, "r");
	if (fp == NULL)
		return;
	while (getline(&line, &len, fp) != -1) {
		char        *s = rmspace(line);
		char        *sp;
		char        *tok;
		depend_atom *a;
		pkgcfg_t    *pc;

		if (*s == '\0' || *s == '#')
			continue;
		tok = strtok_r(s, " \t", &sp);
		if (tok == NULL)
			continue;
		if (strchr(tok, '*') != NULL)
			continue;
		a = atom_explode(tok);
		if (a == NULL) {
			warn("%s: invalid atom '%s'", file, tok);
			continue;
		}
		pc = xzalloc(sizeof(*pc));
		pc->atom = a;
		pc->vals = xstrdup(sp == NULL ? "" : rmspace(sp));
		if (*into == NULL)
			*into = array_new();
		array_append(*into, pc);
	}
	free(line);
	fclose(fp);
}

static void
read_pkgcfg(const char *name, array **into)
{
	char            path[_Q_PATH_MAX];
	struct dirent **dents;
	int             cnt;
	int             i;

	snprintf(path, sizeof(path), "%s/etc/portage/%s", configroot, name);
	cnt = scandir(path, &dents, NULL, alphasort);
	if (cnt >= 0) {
		char sub[_Q_PATH_MAX * 2];

		for (i = 0; i < cnt; i++) {
			if (dents[i]->d_name[0] == '.')
				continue;
			snprintf(sub, sizeof(sub), "%s/%s", path, dents[i]->d_name);
			read_pkgcfg_file(sub, into);
		}
		scandir_free(dents, cnt);
	} else {
		read_pkgcfg_file(path, into);
	}
}

static void
read_package_use_global(void)
{
	char            path[_Q_PATH_MAX];
	struct dirent **dents;
	int             cnt;
	int             i;

	snprintf(path, sizeof(path), "%s/etc/portage/package.use",
			 configroot);
	cnt = scandir(path, &dents, NULL, alphasort);
	if (cnt >= 0) {
		char sub[_Q_PATH_MAX * 2];

		for (i = 0; i < cnt; i++) {
			if (dents[i]->d_name[0] == '.')
				continue;
			snprintf(sub, sizeof(sub), "%s/%s",
					 path, dents[i]->d_name);
			read_package_use_global_file(sub);
		}
		scandir_free(dents, cnt);
	} else {
		read_package_use_global_file(path);
	}
}

/* expand ${VAR}/$VAR references against everything read so far plus
 * the environment, the way the shell would when sourcing make.conf;
 * returns a freshly allocated string */
static char *
expand_config_refs(const char *s)
{
	char   *out  = NULL;
	size_t  olen = 0;
	size_t  ocap = 0;

#define OUTC(C) \
	do { \
		if (olen + 1 >= ocap) { \
			ocap = ocap > 0 ? ocap * 2 : 64; \
			out = xrealloc(out, ocap); \
		} \
		out[olen++] = (C); \
	} while (0)

	while (*s != '\0') {
		if (*s == '\\' && s[1] == '$') {
			OUTC('$');
			s += 2;
			continue;
		}
		if (*s == '$') {
			const char *p     = s + 1;
			bool        brace = *p == '{';
			const char *n     = brace ? p + 1 : p;
			size_t      nl    = strspn(n,
					"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
					"abcdefghijklmnopqrstuvwxyz0123456789_");

			if (nl > 0 && nl < 128 && (!brace || n[nl] == '}')) {
				char        name[128];
				const char *v;

				memcpy(name, n, nl);
				name[nl] = '\0';
				v = all_config_vars != NULL ?
						get_set(name, all_config_vars) : NULL;
				if (v == NULL)
					v = getenv(name);
				if (v != NULL)
					for (; *v != '\0'; v++)
						OUTC(*v);
				s = n + nl + (brace ? 1 : 0);
				continue;
			}
		}
		OUTC(*s);
		s++;
	}
	OUTC('\0');
#undef OUTC
	return out;
}

/* Helper to read a portage file (e.g. make.conf, package.mask), or
 * recursively if it points to a directory (we don't care about EAPI for
 * dirs, basically PMS 5.2.5 EAPI restriction is ignored) */
enum portage_file_type { ENV_FILE, PMASK_FILE };
static void
read_portage_file(const char *file, enum portage_file_type type, void *data)
{
	FILE *fp;
	struct dirent **dents = NULL;
	int dentslen;
	char *s;
	char *p;
	char *buf = NULL;
	size_t buflen = 0;
	size_t line;
	bool incomment;
	size_t cbeg;
	size_t cend;
	char npath[_Q_PATH_MAX * 2];
	int i;
	env_vars *vars = data;
	hash_t *masks = data;

	snprintf(npath, sizeof(npath), "%s%s", portroot, file + 1);
	if ((dentslen = scandir(npath, &dents, NULL, alphasort)) > 0) {
		int di;
		struct dirent *d;

		/* recurse through all files */
		for (di = 0; di < dentslen; di++) {
			d = dents[di];
			if (d->d_name[0] == '.' || d->d_name[0] == '\0' ||
					d->d_name[strlen(d->d_name) - 1] == '~')
				continue;
			snprintf(npath, sizeof(npath), "%s/%s", file, d->d_name);
			read_portage_file(npath, type, data);
		}
		scandir_free(dents, dentslen);
		goto done;
	}

	fp = fopen(npath, "r");
	if (fp == NULL)
		goto done;

	line = 0;
	incomment = false;
	cbeg = 0;
	cend = 0;
	while (getline(&buf, &buflen, fp) != -1) {
		line++;
		rmspace(buf);
		if (*buf == '#') {
			if (!incomment)
				cbeg = cend = line;
			else
				cend = line;
			incomment = true;
			continue;
		}
		incomment = false;
		if (*buf == '\0') {
			cbeg = cend = 0;
			continue;
		}

		if (type == ENV_FILE) {
			size_t curline = line;

			/* Handle "source" keyword */
			if (strncmp(buf, "source ", 7) == 0) {
				const char *sfile = buf + 7;

				if (sfile[0] != '/') {
					/* handle relative paths */
					size_t file_path_len;

					s = q_deconst(strrchr(file, '/'));
					file_path_len = s - file + 1;

					snprintf(npath, sizeof(npath), "%.*s/%s",
							(int)MIN(file_path_len, (size_t)4095),
							file, sfile);
					sfile = npath;
				}

				read_portage_file(sfile, type, data);
				continue;
			}

			/* parse any VAR=value line: every variable is stored
			 * raw in all_config_vars (so e.g. USE_EXPAND member
			 * variables can be resolved for the binpkg index), and
			 * the typed table entries additionally get their
			 * specific handling */
			{
				size_t nlen = strspn(buf,
						"ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_");

				if (nlen == 0 ||
						(buf[nlen] != '=' && buf[nlen] != ' '))
					continue;

				/* make sure we handle spaces between the varname, the =,
				 * and the value:
				 * VAR=val   VAR = val   VAR="val"
				 */
				s = buf + nlen;
				if ((p = strchr(s, '=')) != NULL)
					s = p + 1;
				while (isspace(*s))
					s++;
				if (*s == '"' || *s == '\'') {
					char *endq;
					char q = *s;

					/* make sure we handle spacing/comments after the quote */
					endq = strchr_unescaped(s + 1, q);
					if (!endq) {
						/* if the last char is not a quote,
						 * then we span lines */
						size_t abuflen;
						size_t blen;
						size_t alen;
						char *abuf;

						abuf = NULL;
						/* the outer reader stripped this line's
						 * newline: restore it so joined values keep
						 * their line structure like portage sees it */
						buflen = strlen(buf) + 2;
						buf = xrealloc(buf, buflen);
						blen = buflen - 2;
						buf[blen++] = '\n';
						buf[blen] = '\0';
						while (getline(&abuf, &abuflen, fp) != -1) {
							line++;
							buf = xrealloc(buf, buflen + abuflen);
							endq = strchr_unescaped(abuf, q);
							if (endq)
								*endq = '\0';

							alen = strlen(abuf);
							memcpy(buf + blen, abuf, alen + 1);
							blen += alen;
							buflen += abuflen;

							if (endq)
								break;
						}
						free(abuf);

						if (!endq)
							warn("%s%s:%zu: %.*s: quote mismatch",
									portroot, file + 1, line,
									(int)nlen, buf);

						s = buf + nlen + 2;
					} else {
						*endq = '\0';
						s++;
					}
				} else {
					/* no quotes, so chop the spacing/comments ourselves */
					size_t off = strcspn(s, "# \t\n");
					s[off] = '\0';
				}

				/* expand ${VAR} references immediately like the
				 * shell would; the fetch command templates keep
				 * theirs for runtime evaluation */
				{
					static char *expanded = NULL;

					free(expanded);
					expanded = NULL;
					if (!(nlen == 13 &&
						  strncmp(buf, "QFETCHCOMMAND", 13) == 0) &&
						!(nlen == 14 &&
						  strncmp(buf, "QRESUMECOMMAND", 14) == 0) &&
						!(nlen == 14 &&
						  strncmp(buf, "QFETCH_WRAPPER", 14) == 0) &&
						!(nlen == 13 &&
						  strncmp(buf, "FETCH_WRAPPER", 13) == 0) &&
						strchr(s, '$') != NULL)
					{
						expanded = expand_config_refs(s);
						s = expanded;
					}
				}

				/* remember the raw value of every variable */
				if (nlen < 128) {
					char  vname[128];
					void *prev = NULL;

					memcpy(vname, buf, nlen);
					vname[nlen] = '\0';
					if (all_config_vars == NULL)
						all_config_vars = create_set();
					add_set_value(vname, xstrdup(s), &prev,
								  all_config_vars);
					free(prev);
				}

				for (i = 0; vars[i].name; i++) {
					if (vars[i].name_len != nlen ||
							strncmp(buf, vars[i].name, nlen) != 0)
						continue;
					if (vars[i].from_cli)
						break;
					snprintf(npath, sizeof(npath), "%s%s:%zu:%zu-%zu",
							portroot, file + 1, curline, cbeg, cend);
					set_portage_env_var(&vars[i], s, npath);
					break;
				}
			}
		} else if (type == PMASK_FILE) {
			if (*buf == '-') {
				/* negation/removal, lookup and drop mask if it exists;
				 * note that this only supports exact matches (PMS
				 * 5.2.5) so we don't even have to parse and use
				 * atom-compare here */
				if ((p = hash_delete(masks, buf + 1)) != NULL)
					free(p);
			} else {
				void *e;
				snprintf(npath, sizeof(npath), "%s%s:%zu:%zu-%zu",
						portroot, file + 1, line, cbeg, cend);
				/* if not necessary, but do it for static code analysers
				 * which take into accound that hash_add might
				 * allocate a new set when masks would be NULL, a case
				 * which would never happen */
				if (masks != NULL) {
					p = xstrdup(npath);
					/* hash_add REPLACES the stored value: on a duplicate
					 * atom the hash now holds p, drop the OLD location */
					hash_add(masks, buf, p, &e);
					if (e != NULL)
						free(e);
				}
			}
		}
	}

	fclose(fp);
 done:
	free(buf);

	if (getenv("DEBUG"))
		fprintf(stderr, "read profile %s%s\n", portroot, file + 1);
}

/* Helper to check if a string starts with a prefix. If so, returns
 * true and gets the length of the prefix. Otherwise returns false,
 * leaving the prefix length unmodified. */
static bool
starts_with(const char *str, const char *prefix, size_t *prefix_len)
{
	const char *s;
	const char *p;
	size_t len;

	if (prefix == NULL) {
		/* every string starts with a null string */
		if (prefix_len != NULL)
			*prefix_len = 0;
		return true;
	}
	if (str == NULL)
		/* null string only starts with a null string, and prefix isn't null */
		return false;

	len = 0;
	for (s = str, p = prefix; *s != '\0' && *p != '\0'; ++s, ++p, ++len) {
		if (*s != *p)
			return false;
	}
	if (*p == '\0') {
		if (prefix_len != NULL)
			*prefix_len = len;
		return true;
	}
	return false;
}

/* Helper to figure out inside of which overlay a path is. Returns
 * null if nonesuch is found. */
static const char *
overlay_from_path(const char *path)
{
	size_t n;
	char *overlay;
	size_t max_match = 0;
	const char *found_overlay = NULL;

	/* won't ever match, a location must be absolute */
	if (path[0] != '/')
		return NULL;

	if (portroot[1] == '\0') {
		/* no ROOT usage, simply ignore it */
		array_for_each(overlays, n, overlay) {
			size_t overlay_len;

			if (!starts_with(path, overlay, &overlay_len))
				continue;

			if (overlay_len <= max_match)
				continue;

			max_match = overlay_len;
			found_overlay = overlay;

			if (overlay[overlay_len] == '\0')
				break;
		}
	} else {
		char rootpath[_Q_PATH_MAX];
		char ovrlpath[_Q_PATH_MAX];
		char resolved[_Q_PATH_MAX];

		snprintf(resolved, sizeof(resolved), "%s%s", portroot, &path[1]);
		if (realpath(resolved, rootpath) == NULL)
			memcpy(rootpath, resolved, sizeof(resolved));

		array_for_each(overlays, n, overlay) {
			size_t overlay_len;

			snprintf(resolved, sizeof(resolved), "%s%s", portroot, &overlay[1]);
			if (realpath(resolved, ovrlpath) == NULL)
				memcpy(ovrlpath, resolved, sizeof(resolved));

			if (!starts_with(rootpath, ovrlpath, &overlay_len))
				continue;

			if (overlay_len <= max_match)
				continue;

			max_match = overlay_len;
			found_overlay = overlay;
		}
	}

	/* we must match at least the overlay location; under ROOT the
	 * matched length is measured against the resolved (prefixed)
	 * path, so indexing the raw overlay string with it read out of
	 * bounds, compare lengths instead */
	if (found_overlay != NULL &&
		strlen(found_overlay) > max_match)
	{
		found_overlay = NULL;
	}

	return found_overlay;
}

/* Helper to recursively read stacked make.defaults in profiles */
static void
read_portage_profile_r(const char *profile, env_vars vars[], hash_t *masks,
		set *onpath)
{
	char profile_file[_Q_PATH_MAX * 3];
	char rpath[_Q_PATH_MAX];
	size_t profile_len;
	char *s;
	char *p;
	char *buf = NULL;
	size_t buf_len = 0;
	char *saveptr;

	/* create mutable/appendable copy */
	profile_len = snprintf(profile_file, sizeof(profile_file), "%s/", profile);

	/* check if we have enough space (should always be the case) */
	if (profile_len >= sizeof(profile_file) ||
			sizeof(profile_file) - profile_len <
			sizeof("package.use.stable.force"))
		return;

	if (contains_set(profile, onpath) != NULL) {
		if (!quiet)
			warn("profile parent cycle detected, skipping %s", profile);
		return;
	}
	onpath = add_set(profile, onpath);

	/* first follow all the parents, PMS 5.2.1 defines that it should
	 * treat parent profiles as defaults, that can be overridden by
	 * *this* profile. */
	memcpy(profile_file + profile_len, "parent", sizeof("parent"));
	if (eat_file(profile_file, &buf, &buf_len)) {
		s = strtok_r(buf, "\n", &saveptr);
		for (; s != NULL; s = strtok_r(NULL, "\n", &saveptr)) {
			/* handle repo: notation (not in PMS, referenced in Wiki only?) */
			if ((p = strchr(s, ':')) != NULL) {
				char *overlay;
				char *repo_name;
				size_t n;

				/* split repo from target */
				*p++ = '\0';

				if (s[0] == '\0') {
					/* empty repo name means a repo where the profile is */
					const char* current_overlay = overlay_from_path(profile);
					if (current_overlay == NULL) {
						/* bring back the colon to see the ignored
						 * parent line */
						*(--p) = ':';
						if (!quiet)
							warn("could not figure out current repo "
								 "of profile %s, ignoring parent %s",
							     profile, s);
						continue;
					}
					snprintf(profile_file, sizeof(profile_file),
							"%s/profiles/%s", current_overlay, p);
				} else {
					/* match the repo */
					repo_name = NULL;
					array_for_each(overlays, n, overlay) {
						repo_name = array_get(overlay_names, n);
						if (repo_name != NULL && strcmp(repo_name, s) == 0) {
							snprintf(profile_file, sizeof(profile_file),
									"%s/profiles/%s/", overlay, p);
							break;
						}
						repo_name = NULL;
					}
					if (repo_name == NULL) {
						/* bring back the colon to see the ignored
						 * parent line */
						*(--p) = ':';
						if (!quiet)
							warn("ignoring parent with unknown repo "
								 "in profile %s: %s", profile, s);
						continue;
					}
                                }
			} else {
				snprintf(profile_file + profile_len,
						sizeof(profile_file) - profile_len, "%s", s);
			}
			read_portage_profile_r(
					realpath(profile_file, rpath) == NULL ?
					profile_file : rpath, vars, masks, onpath);
			/* restore original path in case we were repointed by profile */
			if (p != NULL)
				snprintf(profile_file, sizeof(profile_file), "%s/", profile);
		}
	}

	if (buf != NULL)
		free(buf);

	/* now consume *this* profile's make.defaults and package.mask.
	 * time to memcpy them all. probably the time has come to fix
	 * the unsafe sht going on. */
	memcpy(profile_file + profile_len, "make.defaults", sizeof("make.defaults"));
	read_portage_file(profile_file, ENV_FILE, vars);
	memcpy(profile_file + profile_len, "package.mask", sizeof("package.mask"));
	read_portage_file(profile_file, PMASK_FILE, masks);
	memcpy(profile_file + profile_len, "use.mask", sizeof("use.mask"));
	read_use_flag_file(profile_file, &use_mask);
	memcpy(profile_file + profile_len, "use.stable.mask", sizeof("use.stable.mask"));
	read_use_flag_file(profile_file, &use_mask);
	memcpy(profile_file + profile_len, "use.force", sizeof("use.force"));
	read_use_flag_file(profile_file, &use_force);
	memcpy(profile_file + profile_len, "use.stable.force", sizeof("use.stable.force"));
	read_use_flag_file(profile_file, &use_force);
	memcpy(profile_file + profile_len, "package.use", sizeof("package.use"));
	read_pkgcfg_file(profile_file, &pkg_use);
	memcpy(profile_file + profile_len, "package.use.force", sizeof("package.use.force"));
	read_pkgcfg_file(profile_file, &pkg_use_force);
	memcpy(profile_file + profile_len, "package.use.stable.force", sizeof("package.use.stable.force"));
	read_pkgcfg_file(profile_file, &pkg_use_force);
	memcpy(profile_file + profile_len, "package.use.mask", sizeof("package.use.mask"));
	read_pkgcfg_file(profile_file, &pkg_use_mask);
	memcpy(profile_file + profile_len, "package.use.stable.mask", sizeof("package.use.stable.mask"));
	read_pkgcfg_file(profile_file, &pkg_use_mask);

	del_set(profile, onpath, NULL);
}

static void
read_portage_profile(const char *profile, env_vars vars[], hash_t *masks)
{
	set *onpath = create_set();

	read_portage_profile_r(profile, vars, masks, onpath);
	free_set(onpath);
}

env_vars vars_to_read[] = {
#define _Q_EV(t, V, set, lset, d, E) \
{ \
	.name = #V, \
	.name_len = sizeof(#V) - 1, \
	.type = _Q_##t, \
	set, \
	lset, \
	.default_value = d, \
	.src = NULL, \
	.fromenv = E, \
},
#define _Q_EVS(t, V, v, E, D) \
	_Q_EV(t, V, .value.s = &v, .value_len = sizeof(D) - 1, D, E)
#define _Q_EVB(t, V, v, E, D) \
	_Q_EV(t, V, .value.b = &v, .value_len = 0, D, E)
#define _Q_EVT(T, V, v, E, D) \
	_Q_EV(T, V, .value.t = &v, .value_len = 0, D, E)

	_Q_EVS(STR,  ROOT,                portroot,            true,  "/")
	_Q_EVS(ISTR, ACCEPT_LICENSE,      accept_license,      true,  "")
	_Q_EVS(NSTR, INSTALL_MASK,        install_mask,        true,  "")
	_Q_EVS(NSTR, PKG_INSTALL_MASK,    pkg_install_mask,    true,  "")
	_Q_EVS(STR,  ARCH,                portarch,            true,  "")
	_Q_EVS(ISTR, CONFIG_PROTECT,      config_protect,      true,  "/etc")
	_Q_EVS(ISTR, CONFIG_PROTECT_MASK, config_protect_mask, true,  "")
	_Q_EVB(BOOL, NOCOLOR,             nocolor,             true,  NULL)
	_Q_EVT(ISET, FEATURES,            features,            true,  NULL)
	_Q_EVT(ISET, USE,                 ev_use,              true,  NULL)
	_Q_EVS(STR,  EPREFIX,             eprefix,             true,  CONFIG_EPREFIX)
	_Q_EVS(STR,  EMERGE_LOG_DIR,      portlogdir,          true,  CONFIG_EPREFIX "var/log")
	_Q_EVS(STR,  PORTDIR,             main_overlay,        true,  CONFIG_EPREFIX "var/db/repos/gentoo")
	_Q_EVS(STR,  PORTAGE_BINHOST,     binhost,             true,   DEFAULT_PORTAGE_BINHOST)
	_Q_EVS(STR,  PORTAGE_CONFIGROOT,  configroot,          false, CONFIG_EPREFIX)
	_Q_EVS(STR,  PORTAGE_TMPDIR,      port_tmpdir,         true,  CONFIG_EPREFIX "var/tmp/portage/")
	_Q_EVS(STR,  PKGDIR,              pkgdir,              true,  CONFIG_EPREFIX "var/cache/binpkgs/")
	_Q_EVS(STR,  BINPKG_FORMAT,       binpkg_format,       true,  "gpkg")
	_Q_EVS(STR,  BINPKG_COMPRESS,     binpkg_compress,     true,  "")
	_Q_EVS(STR,  BINPKG_COMPRESS_FLAGS, binpkg_compress_flags, true, "")
	_Q_EVS(STR,  QGTREE_COMPRESS,     qgtree_compress,     true,  "zstd:3")
	_Q_EVS(STR,  Q_VDB,               portvdb,             true,  CONFIG_EPREFIX "var/db/pkg")
	_Q_EVS(STR,  Q_EDB,               portedb,             true,  CONFIG_EPREFIX "var/cache/edb")
	_Q_EVS(STR,  QFETCHCOMMAND,       qfetchcommand,       true,  "")
	_Q_EVS(STR,  QRESUMECOMMAND,      qresumecommand,      true,  "")
	_Q_EVS(STR,  QFETCH_WRAPPER,      qfetchwrapper,       true,  "")
	_Q_EVS(STR,  FETCH_WRAPPER,       fetchwrapper,        true,  "")
	_Q_EVS(STR,  CHOST,               chost,               true,  "")
	_Q_EVS(STR,  CBUILD,              cbuild,              true,  "")
	_Q_EVS(ISTR, ACCEPT_KEYWORDS,     accept_keywords,     true,  "")
	_Q_EVS(STR,  ACCEPT_PROPERTIES,   accept_properties,   true,  "")
	_Q_EVS(STR,  ACCEPT_RESTRICT,     accept_restrict,     true,  "")
	_Q_EVS(STR,  GENTOO_MIRRORS,      gentoo_mirrors,      true,  "")
	_Q_EVS(ISTR, IUSE_IMPLICIT,       iuse_implicit,       true,  "")
	_Q_EVS(ISTR, USE_EXPAND,          use_expand,          true,  "")
	_Q_EVS(ISTR, USE_EXPAND_HIDDEN,   use_expand_hidden,   true,  "")
	_Q_EVS(ISTR, USE_EXPAND_IMPLICIT, use_expand_implicit, true,  "")
	_Q_EVS(ISTR, USE_EXPAND_UNPREFIXED, use_expand_unprefixed, true, "")
	_Q_EVS(STR,  ELIBC,               var_elibc,           true,  "")
	_Q_EVS(STR,  KERNEL,              var_kernel,          true,  "")
	_Q_EVB(BOOL, QMERGE_NOCOLOR,      qmerge_nocolor,      true,  NULL)
	_Q_EVS(STR,  QMERGE_JOBS,         qmerge_jobs_conf,    true,  "")
	_Q_EVB(BOOL, QMERGE_PREFETCH,     qmerge_prefetch,     true,  (const char *)1)
	_Q_EVS(STR,  QMERGE_MOVES,        qmerge_moves_conf,   true,  "")
	_Q_EVB(BOOL, QNEWS_ENABLE,        qnews_enable,        true,  NULL)
	_Q_EVB(BOOL, QMERGE_BLOCKERS,     qmerge_blockers,     true,  NULL)
	_Q_EVS(STR,  QETUTO_KEYSERVERS,   qetuto_keyservers_conf, true, "")
	_Q_EVS(STR,  QETUTO_KEYS,         qetuto_keys_conf,    true,  "")
	_Q_EVS(STR,  QETUTO_EXTERNAL_REFRESH, qetuto_external_refresh_conf, true, "0")
	_Q_EVS(NSTR, COLLISION_IGNORE,    collision_ignore,    true,
		   "/lib/modules/* *.py[co] *$py.class")
	_Q_EVS(STR,  QMERGE_LOCAL_PRIORITY, qmerge_local_priority_conf, true, "")
	_Q_EVS(STR,  QMERGE_LENIENT_UPGRADE, qmerge_lenient_conf, true, "")
	_Q_EVS(STR,  QMERGE_KEEP_GOING,    qmerge_keep_going_conf, true, "")
	_Q_EVS(STR,  QMERGE_BINPKG_RESPECT_USE, qmerge_respect_use_conf, true, "")
	_Q_EVS(STR,  QMERGE_REBUILT_BINARIES, qmerge_rebuilt_conf, true, "")
	_Q_EVS(STR,  BINPKG_GPG_VERIFY_GPG_HOME, binpkg_gpg_verify_gpg_home, true,
		   CONFIG_EPREFIX "etc/portage/gnupg")
	_Q_EVS(STR,  PORTAGE_BINPKG_TAR_OPTS, binpkg_tar_opts, true, "")
	_Q_EVS(STR,  ACCEPT_CHOSTS,        accept_chosts,       true,  "")
	_Q_EVS(STR,  BINPKG_GPG_SIGNING_BASE_COMMAND, binpkg_gpg_signing_base_command,
		   true, "/usr/bin/flock /run/lock/portage-binpkg-gpg.lock "
		   "/usr/bin/gpg --sign --armor [PORTAGE_CONFIG]")
	_Q_EVS(STR,  BINPKG_GPG_SIGNING_DIGEST, binpkg_gpg_signing_digest, true,
		   "SHA512")
	_Q_EVS(STR,  BINPKG_GPG_SIGNING_GPG_HOME, binpkg_gpg_signing_gpg_home, true, "")
	_Q_EVS(STR,  BINPKG_GPG_SIGNING_KEY, binpkg_gpg_signing_key, true,  "")
	{ NULL, 0, _Q_BOOL, { NULL }, 0, NULL, NULL, NULL, false, }

#undef _Q_EV
#undef _Q_EVS
#undef _Q_EVB
};
hash_t *package_masks = NULL;
hash_t *package_unmasks = NULL;

/* Handle a single file in the repos.conf format. */
static void
read_one_repos_conf(const char *repos_conf, char **primary)
{
	char   pth[_Q_PATH_MAX];
	char  *main_repo;
	char  *repo;
	char  *buf = NULL;
	size_t buf_len = 0;
	char  *s = NULL;  /* pacify compiler */
	char  *p;
	char  *q;
	char  *r;
	char  *e;
	bool   do_trim;
	bool   is_default = false;  /* pacify compiler; set by every [section] */

	snprintf(pth, sizeof(pth), "%s%s", portroot, repos_conf);
	if (getenv("DEBUG"))
		fprintf(stderr, "  parse %s\n", pth);

	if (!eat_file(pth, &buf, &buf_len)) {
		if (buf != NULL)
			free(buf);
		return;
	}
	snprintf(pth, sizeof(pth), "/%s", repos_conf);

	main_repo = NULL;
	repo = NULL;
	for (p = strtok_r(buf, "\n", &s); p != NULL; p = strtok_r(NULL, "\n", &s))
	{
		/* trim trailing whitespace, remove comments, locate =, scanning
		 * backwards to the front of the string */
		do_trim = true;
		e = NULL;
		r = q = p + strlen(p) - 1;
		for (;;) {
			if (do_trim && isspace((int)*q)) {
				*q = '\0';
				if (q > p)
					r = q - 1;
			} else if (*q == '#') {
				do_trim = true;
				*q = '\0';
				e = NULL;
				if (q > p)
					r = q - 1;
			} else {
				if (*q == '=')
					e = q;
				do_trim = false;
			}
			if (q == p)
				break;
			q--;
		}
		/* make q point to the last char */
		q = r;

		if (*p == '[' && *q == ']') {  /* section header */
			repo = p + 1;
			*q = '\0';
			is_default = strcmp(repo, "DEFAULT") == 0;
			continue;
		} else if (*p == '\0') {       /* empty line */
			continue;
		} else if (e == NULL) {        /* missing = */
			continue;
		} else if (repo == NULL) {     /* not in a section */
			continue;
		}

		/* trim off whitespace before = */
		for (r = e; r > p && isspace((int)r[-1]); r--)
			r[-1] = '\0';
		/* and after the = */
		for (*e++ = '\0'; e < q && isspace((int)*e); e++)
			;

		if (is_default && strcmp(p, "main-repo") == 0) {
			main_repo = e;
		} else if (!is_default && strcmp(p, "location") == 0) {
			void *ele;
			size_t n;
			char *overlay;

			array_for_each(overlay_names, n, overlay) {
				if (strcmp(overlay, repo) == 0)
					break;
				overlay = NULL;
			}
			if (overlay != NULL) {
				/* replace overlay */
				array_delete(overlay_src, n, NULL);
				array_append_strcpy(overlay_src, pth);

				ele = array_remove(overlay_names, n);
				array_append(overlay_names, ele);

				array_delete(overlays, n, NULL);
				ele = array_append_strcpy(overlays, e);
			} else {
				ele     = array_append_strcpy(overlays, e);
				overlay = array_append_strcpy(overlay_names, repo);
				array_append_strcpy(overlay_src, pth);
			}
			if (main_repo && strcmp(repo, main_repo) == 0)
				*primary = overlay;
		}
	}

	free(buf);
}

/* Handle a possible directory of files. */
static void
read_repos_conf(const char *repos_conf, char **primary)
{
	char            top_conf[_Q_PATH_MAX];
	struct dirent **confs = NULL;
	int             i;
	int             count;

	snprintf(top_conf, sizeof(top_conf), "%s%s%s",
			 portroot, configroot, repos_conf);
	if (getenv("DEBUG"))
		fprintf(stderr, "repos.conf.d scanner %s\n", top_conf);
	count = scandir(top_conf, &confs, NULL, alphasort);
	if (count == -1) {
		if (errno == ENOTDIR)
			read_one_repos_conf(top_conf + strlen(portroot), primary);
	} else {
		char sub_conf[_Q_PATH_MAX * 2];

		for (i = 0; i < count; i++)
		{
			const char *name = confs[i]->d_name;
			struct stat st;

			/* skip self, parent, and "hidden" files */
			if (name[0] == '.' || name[0] == '\0')
				continue;

			/* Exclude backup files (aka files with ~ as postfix). */
			if (name[strlen(name) - 1] == '~')
				continue;

			snprintf(sub_conf, sizeof(sub_conf), "%s/%s", top_conf, name);

			/* skip non-files */
			if (stat(sub_conf, &st) != 0 ||
				!S_ISREG(st.st_mode))
				continue;

			read_one_repos_conf(sub_conf + strlen(portroot), primary);
		}
		scandir_free(confs, count);
	}
}

static void
initialize_portage_env(void)
{
	char        pathbuf[_Q_PATH_MAX];
	char        rpathbuf[_Q_PATH_MAX];
	const char *s;
	char       *primary_overlay;
	env_vars   *var;
	size_t      i;

	package_masks = hash_new();
	package_unmasks = hash_new();

	/* figure out where to find our config files, we need to do this
	 * before handling the files, as it specifies where to find them */
	s = getenv("PORTAGE_CONFIGROOT");
	if (s == NULL)
	{
		s = vars_to_read[14].default_value;
		primary_overlay = q_deconst("built-in");
	}
	else
	{
		primary_overlay = q_deconst("PORTAGE_CONFIGROOT");
	}

	/* allow configroot to be empty */
	if (s[0] != '/' &&
		s[0] != '\0')
		err("PORTAGE_CONFIGROOT must be an absolute path");

	/* rstrip /-es */
	i = strlen(s);
	while (i > 0 &&
		   s[i - 1] == '/')
		i--;
	/* construct configroot, ensure it is always at least / (contrast to
	 * what we accept above) so in code we can always assume
	 * configroot + 1 is valid */
	snprintf(pathbuf, sizeof(pathbuf), "%s%.*s",
			 i == 0 ? "/" : "",
			 (int)MIN(i, sizeof(pathbuf) - 2), s);
	set_portage_env_var(&vars_to_read[14], pathbuf, primary_overlay);

	/* read overlays first so we can resolve repo references in profile
	 * parent files (non PMS feature?) */
	primary_overlay = NULL;
	read_repos_conf("/usr/share/portage/config/repos.conf", &primary_overlay);
	read_repos_conf("/etc/portage/repos.conf", &primary_overlay);

	/* consider Portage's defaults */
	snprintf(pathbuf, sizeof(pathbuf),
			 "%s/usr/share/portage/config/make.globals", configroot);
	read_portage_file(pathbuf, ENV_FILE, vars_to_read);

	/* start with base masks, Portage behaviour PMS 5.2.8 */
	if (primary_overlay != NULL) {
		char *overlay;
		size_t n;
		array_for_each(overlay_names, n, overlay) {
			if (overlay == primary_overlay) {
				snprintf(pathbuf, sizeof(pathbuf), "%s/profiles/package.mask",
						(char *)array_get(overlays, n));
				read_portage_file(pathbuf, PMASK_FILE, package_masks);
				break;
			}
		}
	}

	/* follow all the stacked profiles */
	snprintf(pathbuf, sizeof(pathbuf), "%s%s/etc/make.profile",
			 portroot, configroot + 1);
	read_portage_profile(
			realpath(pathbuf, rpathbuf) == NULL ? pathbuf : rpathbuf,
			vars_to_read, package_masks);
	snprintf(pathbuf, sizeof(pathbuf), "%s%s/etc/portage/make.profile",
			 portroot, configroot + 1);
	read_portage_profile(
			realpath(pathbuf, rpathbuf) == NULL ? pathbuf : rpathbuf,
			vars_to_read, package_masks);

	/* now read all Portage's config files */
	snprintf(pathbuf, sizeof(pathbuf), "%s/etc/make.conf",
			 configroot);
	read_portage_file(pathbuf, ENV_FILE, vars_to_read);
	snprintf(pathbuf, sizeof(pathbuf), "%s/etc/portage/make.conf",
			 configroot);
	read_portage_file(pathbuf, ENV_FILE, vars_to_read);

	/* user package.mask (/etc/portage; read_portage_file recurses the dir
	 * form).  Profile/repo masks were already loaded above; these stack. */
	snprintf(pathbuf, sizeof(pathbuf), "%s/etc/portage/package.mask",
			 configroot);
	read_portage_file(pathbuf, PMASK_FILE, package_masks);

	/* user package.unmask: overrides matching mask entries */
	snprintf(pathbuf, sizeof(pathbuf), "%s/etc/portage/package.unmask",
			 configroot);
	read_portage_file(pathbuf, PMASK_FILE, package_unmasks);

	/* global wildcard package.use entries override make.conf USE */
	read_package_use_global();
	/* per-atom package.use entries, for the wanted-USE computation */
	read_pkgcfg("package.use", &pkg_use);

	/* per-package keyword acceptance (GLEP 53 visibility) */
	read_pkgcfg("package.accept_keywords", &pkg_accept_keywords);
	read_pkgcfg("package.keywords", &pkg_accept_keywords);

	/* license acceptance (GLEP 23 visibility) */
	read_license_groups();
	read_pkgcfg("package.license", &pkg_license);

	/* finally, check the env */
	for (i = 0; vars_to_read[i].name; i++)
	{
		if (!vars_to_read[i].fromenv)
			continue;

		var = &vars_to_read[i];
		if (var->from_cli)
			continue;
		s   = getenv(var->name);
		if (s != NULL)
			set_portage_env_var(var, s, var->name);
	}

	/* special snowflake, NO_COLOR is apparently some standard now,
	 * accept it (as override of NOCOLOR) */
	s = getenv("NO_COLOR");
	if (s != NULL)
		set_portage_env_var(&vars_to_read[7], s, "NO_COLOR");

	/* expand any nested variables e.g. PORTDIR=${EPREFIX}/usr/portage */
	for (i = 0; vars_to_read[i].name; ++i) {
		char *svar;

		var = &vars_to_read[i];
		if (var->type != _Q_STR && var->type != _Q_NSTR)
			continue;

		/* never expand fetch command templates here: their ${URI},
		 * ${DISTDIR} and ${FILE} are runtime variables for the spawned
		 * shell (escaped as \$ in the config, which this parser does not
		 * interpret) */
		if (strcmp(var->name, "QFETCHCOMMAND") == 0 ||
				strcmp(var->name, "QRESUMECOMMAND") == 0 ||
				strcmp(var->name, "QFETCH_WRAPPER") == 0 ||
				strcmp(var->name, "FETCH_WRAPPER") == 0)
			continue;

		while ((svar = strchr(*var->value.s, '$'))) {
			env_vars *evar;
			bool brace;
			const char *sval;
			size_t slen, pre_len, var_len, post_len;
			char byte;

			pre_len = svar - *var->value.s;

			/* First skip the leading "${" */
			s = ++svar;
			brace = (*svar == '{');
			if (brace)
				s = ++svar;

			/* Now skip the variable name itself */
			while (isalnum(*svar) || *svar == '_')
				++svar;

			/* Finally skip the trailing "}" */
			if (brace && *svar != '}') {
				warn("invalid variable setting: %s\n", *var->value.s);
				break;
			}

			var_len = svar - s + 1 + (brace ? 2 : 0);

			byte = *svar;
			*svar = '\0';

			/* Don't try to expand ourselves */
			if (strcmp(var->name, s) != 0) {
				evar = get_portage_env_var(vars_to_read, s);
				if (evar) {
					sval = *evar->value.s;
				} else {
					sval = getenv(s);
					if (!sval)
						sval = "";
				}
			} else {
				sval = "";
			}
			*svar = byte;
			slen = strlen(sval);
			post_len = strlen(svar + !!brace);
			*var->value.s = xrealloc(*var->value.s,
					pre_len + MAX(var_len, slen) + post_len + 1);

			/*
			 * VAR=XxXxX	(slen = 5)
			 * FOO${VAR}BAR
			 * pre_len = 3
			 * var_len = 6
			 * post_len = 3
			 */
			memmove(*var->value.s + pre_len + slen,
				*var->value.s + pre_len + var_len,
				post_len + 1);
			memcpy(*var->value.s + pre_len, sval, slen);
		}
	}

	/* handle PORTDIR and primary_overlay to get a unified
	 * administration in overlays */
	{
		const char *overlay;
		var = &vars_to_read[12];  /* PORTDIR */

		if (strcmp(var->src, STR_DEFAULT) != 0 ||
			array_cnt(overlays) == 0)
		{
			overlay = overlay_from_path(main_overlay);

			if (overlay == NULL) {  /* add PORTDIR to overlays */
				char *ovcopy = xstrdup(main_overlay);

				overlay = ovcopy;
				array_append(overlays, ovcopy);
				array_append_strcpy(overlay_names, "<PORTDIR>");
				array_append_strcpy(overlay_src, var->src);
			} else {
				/* ignore make.conf and/or env setting origin if defined by
				 * repos.conf since the former are deprecated */
			}
			free(main_overlay);
			main_overlay = NULL;  /* now added to overlays */
		} else {
			free(main_overlay);
		}

		/* set main_overlay to the one pointed to by repos.conf, if any */
		i = 0;
		if (primary_overlay != NULL) {
			array_for_each(overlay_names, i, overlay) {
				if (overlay == primary_overlay)
					break;
				overlay = NULL;
			}
			/* if no explicit overlay was flagged as main, take the
			 * first one */
			if (overlay == NULL)
				i = 0;
		}
		main_overlay = array_get(overlays, i);
		/* set source for PORTDIR var */
		free(var->src);
		overlay = array_get(overlay_src, i);
		if (overlay == NULL)
			overlay = "???";
		var->src = xstrdup(overlay);
	}

	/* Make sure ROOT always ends in a slash */
	var = &vars_to_read[0];  /* ROOT */
	if (var->value_len == 0 || (*var->value.s)[var->value_len - 1] != '/') {
		portroot = xrealloc(portroot, var->value_len + 2);
		portroot[var->value_len] = '/';
		portroot[var->value_len + 1] = '\0';
	}

	if (getenv("DEBUG")) {
		for (i = 0; vars_to_read[i].name; ++i) {
			var = &vars_to_read[i];
			switch (var->type) {
				case _Q_BOOL:
					fprintf(stderr, "%s = %d\n", var->name, *var->value.b);
					break;
				case _Q_STR:
				case _Q_NSTR:
				case _Q_ISTR:
					fprintf(stderr, "%s = %s\n", var->name, *var->value.s);
					break;
				case _Q_ISET: {
					array *vals;
					char  *val;
					size_t n;

					fprintf(stderr, "%s = ", var->name);
					vals = set_keys(*var->value.t);
					array_for_each(vals, n, val) {
						fprintf(stderr, "%s ", val);
					}
					fprintf(stderr, "\n");
					array_free(vals);
				}	break;
			}
		}
	}

	if (nocolor) {
		color_clear();
		setenv("NOCOLOR", "true", 1);
	} else {
		color_remap();
		setenv("NOCOLOR", "false", 1);
	}
}

int main(int argc, char **argv)
{
	struct stat st;
	struct winsize winsz;
	char *overlay = NULL;
	int i;

	warnout = stderr;
	IF_DEBUG(init_coredumps());
	argv0 = argv[0];

	/* ensure any err/warn doesn't use unitialised vars */
	color_clear();

	overlays      = array_new();
	overlay_names = array_new();
	overlay_src   = array_new();

	/* initialise all the properties with their default value */
	for (i = 0; vars_to_read[i].name; ++i) {
		env_vars *var = &vars_to_read[i];
		switch (var->type) {
			case _Q_BOOL:  *var->value.b = var->default_value;           break;
			case _Q_STR:
			case _Q_NSTR:
			case _Q_ISTR:  *var->value.s = xstrdup(var->default_value);  break;
			case _Q_ISET:  *var->value.t = (set *)q_deconst(var->default_value);    break;
		}
		var->src = xstrdup(STR_DEFAULT);
	}

	/* disable colours when not writing to a terminal */
	twidth = 0;
	nocolor = false;
	if (fstat(fileno(stdout), &st) != -1) {
		if (!isatty(fileno(stdout))) {
			nocolor = true;
		} else {
			if ((getenv("TERM") == NULL) ||
					(strcmp(getenv("TERM"), "dumb") == 0))
				nocolor = true;
			if (ioctl(0, TIOCGWINSZ, &winsz) == 0 && winsz.ws_col > 0)
				twidth = (int)winsz.ws_col;
		}
	} else {
		nocolor = true;
	}
	if (nocolor)
		set_portage_env_var(&vars_to_read[7], "true", "terminal"); /* NOCOLOR */

	/* We can use getopt here, but only in POSIX mode (which stops at
	 * the first non-option argument) because otherwise argv is
	 * modified, this basically sulks, because ideally we parse and
	 * handle the common options here.  Because we are parsing profiles
	 * and stuff at this point we need -q for bug #735134, and
	 * --root/--overlay so do lame matching for that */
	for (i = 1; i < argc; i++) {
		if (argv[i] != NULL && argv[i][0] == '-') {
			if (argv[i][1] == '-') {
				if (strcmp(&argv[i][2], "quiet") == 0) {
					setup_quiet();
				} else if (strcmp(&argv[i][2], "root") == 0 &&
						 argv[i + 1] != NULL)
				{
					char  realroot[_Q_PATH_MAX];
					char *root;
					if (realpath(argv[i + 1], realroot) != NULL)
						root = realroot;
					else
						errp("--root argument could not be resolved");
					set_portage_env_var(&vars_to_read[0], root,
										"command line");  /* ROOT */
					vars_to_read[0].from_cli = true;
				} else if (strcmp(&argv[i][2], "overlay") == 0 &&
						   argv[i + 1] != NULL)
				{
					overlay = argv[i + 1];
				}
			} else {
				char *p;

				/* must handle combinations of options like -Rq :( */
				for (p = &argv[i][1]; *p != '\0'; p++) {
					switch (*p) {
						case 'q':
							setup_quiet();
							break;
						default:
							break;
					}
				}
			}
		}
	}

	/* same for env-based fallback */
	if (getenv("PORTAGE_QUIET") != NULL)
		setup_quiet();

	initialize_portage_env();

	/* select or implicitly create overlay when given */
	if (overlay != NULL)
	{
		char buf[_Q_PATH_MAX];
		const char *match;
		char *oname;
		size_t n;

		if (overlay[0] != '/' &&
			getcwd(buf, sizeof(buf)) != NULL)
		{
			size_t len = strlen(buf);

			if (len < sizeof(buf) - 2)
				snprintf(buf + len, sizeof(buf) - len,
						 "/%s", overlay);
			/* first try as relative path */
			match = overlay_from_path(buf);
			if (match == NULL)
			{
				/* then as overlay name */
				array_for_each(overlay_names, n, oname)
				{
					if (strcmp(oname, overlay) == 0)
					{
						match = array_get(overlays, n);
						break;
					}
				}
			}

			if (match == NULL)
				err("no such overlay '%s'", overlay);
		}
		else
		{
			match = overlay_from_path(overlay);
			if (match == NULL)
			{
				/* this is an absolute path, so create it as overlay,
				 * which allows for easy testing */
				match = array_append_strcpy(overlays, overlay);

				array_append_strcpy(overlay_names, "implicit");
				array_append_strcpy(overlay_src,   "--overlay");
			}
		}

		/* at this point match should always be set to something */
		array_for_each_rev(overlays, n, oname)
		{
			if (oname != match)
			{
				array_delete(overlays,      n, NULL);
				array_delete(overlay_names, n, NULL);
				array_delete(overlay_src,   n, NULL);
			}
		}
	}

	optind = 0;
	i = q_main(argc, argv);

	array_deepfree(overlays, NULL);
	array_deepfree(overlay_names, NULL);
	array_deepfree(overlay_src, NULL);

	if (warnout != stderr)
		fclose(warnout);

	return i;
}
