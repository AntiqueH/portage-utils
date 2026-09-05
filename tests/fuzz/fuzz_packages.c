/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "atom.h"
#include "tree.h"

const char *argv0 = "fuzz_packages";
FILE *warnout;

static char idxpath[4096];

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

static char fdir[4096];

int
LLVMFuzzerInitialize(int *argc, char ***argv)
{
	char tmpl[] = "/tmp/qfuzzpkgXXXXXX";

	(void)argc;
	(void)argv;
	warnout = fopen("/dev/null", "we");
	if (warnout == NULL)
		warnout = stderr;
	if (mkdtemp(tmpl) == NULL)
		exit(1);
	snprintf(fdir, sizeof(fdir), "%s", tmpl);
	snprintf(idxpath, sizeof(idxpath), "%s/Packages", fdir);
	return 0;
}

static int
fuzz_pkg_cb(tree_pkg_ctx *pkg, void *priv)
{
	atom_ctx *a;

	(void)priv;
	a = tree_pkg_atom(pkg, true);
	if (a != NULL) {
		char buf[1024];

		atom_to_string_r(buf, sizeof(buf), a);
	}
	(void)tree_pkg_meta(pkg, Q_SLOT);
	(void)tree_pkg_meta(pkg, Q_RDEPEND);
	(void)tree_pkg_meta(pkg, Q_USE);
	(void)tree_pkg_meta(pkg, Q_IUSE);
	(void)tree_pkg_meta(pkg, Q_KEYWORDS);
	(void)tree_pkg_meta(pkg, Q_LICENSE);
	(void)tree_pkg_meta(pkg, Q_PATH);
	(void)tree_pkg_meta(pkg, Q_MD5);
	(void)tree_pkg_meta(pkg, Q_SIZE);
	(void)tree_pkg_meta(pkg, Q_BUILD_ID);
	(void)tree_pkg_meta(pkg, Q_repository);
	return 0;
}

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	FILE     *f;
	tree_ctx *t;

	if (size > 262144)
		return 0;
	f = fopen(idxpath, "we");
	if (f == NULL)
		return 0;
	if (size > 0)
		fwrite(data, 1, size, f);
	fclose(f);

	t = tree_new("/", fdir, TREETYPE_BINPKG, true);
	if (t != NULL) {
		tree_foreach_pkg_fast(t, fuzz_pkg_cb, NULL, NULL);
		tree_close(t);
	}

	unlink(idxpath);
	return 0;
}
