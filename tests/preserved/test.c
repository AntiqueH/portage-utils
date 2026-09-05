/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * Registry test, register/unregister funcs, prune func.
 * Testing whether the preservation of libs .c works.
 * We probably need some dozen examples here, things can vary a lot.
 */

#include "main.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>

#include "array.h"
#include "preserved.h"

const char *argv0;
FILE *warnout;

static int fails = 0;

static void
check(bool ok, const char *desc)
{
	printf("%s: %s\n", ok ? "PASS" : "FAIL", desc);
	if (!ok)
		fails++;
}

int main(int argc, char *argv[])
{
	const char      *dir = argc > 1 ? argv[1] : ".";
	char             reg_path[4096];
	char             p1[4096];
	char             p2[4096];
	preserved_reg   *reg;
	array           *paths;
	array           *ents;
	preserved_entry *pe;

	(void)argc;
	argv0 = argv[0];
	warnout = stderr;

	snprintf(reg_path, sizeof(reg_path), "%s/preserved_libs_registry", dir);

	if (argc > 2 && strcmp(argv[2], "oracle") == 0) {
		reg = preserved_open(reg_path);
		paths = array_new();
		array_append(paths, (void *)"/usr/lib64/lib\"quote\ttab.so.2");
		preserved_register(reg, "dev-libs/esc-2.0-r1", "esc/sub", "42",
						   paths);
		array_free(paths);
		if (!preserved_store(reg))
			return 1;
		preserved_close(reg);
		return 0;
	}

	reg = preserved_open(reg_path);
	check(reg != NULL, "open fresh registry");
	check(preserved_count(reg) == 0, "fresh registry is empty");

	paths = array_new();
	array_append(paths, (void *)"/usr/lib64/libfoo.so.1.2.3");
	array_append(paths, (void *)"/usr/lib64/libfoo.so.1");
	preserved_register(reg, "dev-libs/foo-1.2.3", "0", " 41 \n", paths);
	array_free(paths);

	paths = array_new();
	array_append(paths, (void *)"/usr/lib64/lib\"quote\ttab.so.2");
	preserved_register(reg, "dev-libs/esc-2.0-r1", "esc/sub", "42", paths);
	array_free(paths);

	check(preserved_count(reg) == 2, "two entries registered");
	check(preserved_store(reg), "store");
	preserved_close(reg);

	reg = preserved_open(reg_path);
	check(preserved_count(reg) == 2, "reload finds two entries");
	ents = preserved_entries(reg);
	pe = array_get(ents, 0);
	check(pe != NULL && strcmp(pe->cps, "dev-libs/esc:esc/sub") == 0,
		  "sorted first key is dev-libs/esc:esc/sub");
	pe = array_get(ents, 1);
	check(pe != NULL && strcmp(pe->cps, "dev-libs/foo:0") == 0,
		  "second key is dev-libs/foo:0");
	check(pe != NULL && strcmp(pe->counter, "41") == 0,
		  "counter normalized to 41");
	check(pe != NULL && array_cnt(pe->paths) == 2 &&
		  strcmp((char *)array_get(pe->paths, 0),
				 "/usr/lib64/libfoo.so.1") == 0,
		  "paths sorted, symlink name first");

	preserved_unregister(reg, "dev-libs/foo-1.2.3", "0", "999");
	check(preserved_count(reg) == 2, "unregister with wrong counter is a no-op");
	preserved_unregister(reg, "dev-libs/foo-1.2.3", "0", "41");
	check(preserved_count(reg) == 1, "unregister with matching cpv+counter removes");
	check(preserved_store(reg), "store after unregister");
	preserved_close(reg);

	snprintf(p1, sizeof(p1), "%s/usr/lib64", dir);
	if (system("true") != 0)
		return 1;
	{
		char cmd[8192];

		snprintf(cmd, sizeof(cmd), "mkdir -p '%s'", p1);
		if (system(cmd) != 0)
			return 1;
	}
	snprintf(p1, sizeof(p1), "%s/usr/lib64/libbar.so.3.0.0", dir);
	snprintf(p2, sizeof(p2), "%s/usr/lib64/libbar.so.3", dir);
	{
		FILE *f = fopen(p1, "w");

		if (f == NULL)
			return 1;
		fputs("x", f);
		fclose(f);
	}
	if (symlink("libbar.so.3.0.0", p2) != 0 && access(p2, F_OK) != 0)
		return 1;

	reg = preserved_open(reg_path);
	paths = array_new();
	array_append(paths, (void *)"/usr/lib64/libbar.so.3.0.0");
	array_append(paths, (void *)"/usr/lib64/libbar.so.3");
	array_append(paths, (void *)"/usr/lib64/libgone.so.9");
	preserved_register(reg, "dev-libs/bar-3.0.0", "0", "43", paths);
	array_free(paths);

	preserved_prune(reg, dir);
	ents = preserved_entries(reg);
	pe = NULL;
	{
		size_t           i;
		preserved_entry *e;

		array_for_each(ents, i, e)
			if (strcmp(e->cps, "dev-libs/bar:0") == 0)
				pe = e;
	}
	check(pe != NULL && array_cnt(pe->paths) == 2,
		  "prune drops missing path, keeps file and its symlink");

	unlink(p1);
	preserved_prune(reg, dir);
	pe = NULL;
	{
		size_t           i;
		preserved_entry *e;

		array_for_each(ents, i, e)
			if (strcmp(e->cps, "dev-libs/bar:0") == 0)
				pe = e;
	}
	check(pe == NULL, "prune drops entry when real file gone (dangling symlink)");
	check(preserved_store(reg), "store after prune");
	preserved_close(reg);

	return fails == 0 ? 0 : 1;
}