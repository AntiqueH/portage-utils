/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 */
/* the configuration state the USE/IUSE evaluators read: the effective
 * global USE, the profile masks/forces, the per-package.use overrides,
 * the USE_EXPAND group definitions and the raw config vars (for group
 * values like PYTHON_TARGETS). All fields point at state owned by the
 * caller. Expand_pfxs and hidden are lazily-built caches owned by the
 * ctx (freed with use_ctx_free). */

#ifndef USEFLAGS_H
#define USEFLAGS_H 1

#include <stdbool.h>

#include "atom.h"
#include "array.h"
#include "set.h"
#include "tree.h"

typedef struct {
	depend_atom *atom;
	char        *vals;
} pkgcfg_t;

struct use_expand_pfx {
	char *pfx;
	char *var;
};


struct use_ctx {
	set   *ev_use;
	set   *ev_use_neg;
	set   *use_mask;
	set   *use_force;
	array *pkg_use;
	array *pkg_use_force;
	array *pkg_use_mask;
	set   *all_config_vars;
	const char *use_expand;
	const char *use_expand_implicit;
	const char *use_expand_hidden;

	array *expand_pfxs;
	set   *hidden;
};

void use_ctx_free(struct use_ctx *uc);


const struct use_expand_pfx *uc_expand_group(struct use_ctx *uc,
		const char *tok, const char **suffix);


bool uc_expand_group_hidden(struct use_ctx *uc, const char *var);


int uc_pkg_flag_override(depend_atom *pa, const char *tok, array *lst);


bool uc_use_wanted(struct use_ctx *uc, depend_atom *pa, const char *tok,
		bool def_on);


int uc_use_mismatch(struct use_ctx *uc, tree_pkg_ctx *pkg);


char *uc_use_drift(tree_pkg_ctx *bpkg, tree_pkg_ctx *ipkg);

#endif