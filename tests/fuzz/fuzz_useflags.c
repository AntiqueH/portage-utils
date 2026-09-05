/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * Fuzz the USE/IUSE configuration evaluators (libq/useflags.c). The
 * flag tokens come from a remote Packages index (a binpkg's USE/IUSE
 * fields), so they are attacker-influenced. The group-prefix slicing,
 * package.use override matching and USE_EXPAND value lookup must not
 * read out of bounds or loop on hostile tokens.
 *
 * A fixed but realistic config context is built practically once.
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "atom.h"
#include "array.h"
#include "set.h"
#include "useflags.h"

const char *argv0 = "fuzz_useflags";
FILE *warnout;

static struct use_ctx uc;
static struct use_ctx uc_star;
static depend_atom    *g_atom;

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

static array *
one_pkgcfg(const char *atomstr, const char *vals)
{
	array    *a  = array_new();
	pkgcfg_t *pc = malloc(sizeof(*pc));

	pc->atom = atom_explode(atomstr);
	pc->vals = strdup(vals);
	array_append(a, pc);
	return a;
}

int
LLVMFuzzerInitialize(int *argc, char ***argv)
{
	(void)argc;
	(void)argv;
	warnout = fopen("/dev/null", "we");
	if (warnout == NULL)
		warnout = stderr;

	memset(&uc, 0, sizeof(uc));
	uc.ev_use = create_set();
	add_set("nls", uc.ev_use);
	add_set("opengl", uc.ev_use);
	uc.ev_use_neg = create_set();
	add_set("handbook", uc.ev_use_neg);
	add_set("python_targets_python3_11", uc.ev_use_neg);
	uc.use_mask = create_set();
	add_set("hostname", uc.use_mask);
	uc.use_force = create_set();
	add_set("abi_x86_64", uc.use_force);
	uc.pkg_use       = one_pkgcfg("cat/pkg", "foo -bar");
	uc.pkg_use_force = one_pkgcfg("cat/pkg", "seccomp");
	uc.pkg_use_mask  = one_pkgcfg("cat/pkg", "python_targets_python3_15");
	uc.all_config_vars = create_set();
	add_set_value("PYTHON_TARGETS", strdup("python3_12 python3_13"),
				  NULL, uc.all_config_vars);
	add_set_value("ABI_X86", strdup("64"), NULL, uc.all_config_vars);
	uc.use_expand          = "PYTHON_TARGETS ABI_X86 L10N";
	uc.use_expand_implicit = "ABI_X86";
	uc.use_expand_hidden   = "ABI_X86";

	uc_star = uc;
	uc_star.expand_pfxs = NULL;
	uc_star.hidden      = NULL;
	uc_star.ev_use_neg  = create_set();
	add_set("*", uc_star.ev_use_neg);

	g_atom = atom_explode("cat/pkg-1.0");
	return 0;
}

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char       *tok;
	const char *sfx = NULL;

	if (size > 4096)
		return 0;
	tok = malloc(size + 1);
	if (tok == NULL)
		return 0;
	memcpy(tok, data, size);
	tok[size] = '\0';

	(void)uc_expand_group(&uc, tok, &sfx);
	(void)uc_expand_group_hidden(&uc, tok);
	(void)uc_pkg_flag_override(g_atom, tok, uc.pkg_use);
	(void)uc_use_wanted(&uc, g_atom, tok, false);
	(void)uc_use_wanted(&uc, g_atom, tok, true);
	(void)uc_use_wanted(&uc_star, g_atom, tok, true);

	free(tok);
	return 0;
}