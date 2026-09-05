/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * Fuzz the NEEDED.ELF.2 parser and the linkage queries (libq/linkage.c):
 * - The blob is VDB metadata written by whatever built the binpkg, so
 * field counts, empty fields and separator abuse must not read out of
 * bounds.
 *
 * Input: a NEEDED.ELF.2 blob; first line's soname (if any) is queried
 * back through the provider/revdep lookups.
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "array.h"
#include "linkage.h"

const char *argv0 = "fuzz_needed";
FILE *warnout;

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char        *buf;
	linkage_map *map;
	linkage_pkg *lp;

	if (warnout == NULL)
		warnout = stderr;
	if (size > 1 << 20)
		return 0;

	buf = malloc(size + 1);
	if (buf == NULL)
		return 0;
	memcpy(buf, data, size);
	buf[size] = '\0';

	map = linkage_new();
	linkage_add_pkg(map, "fuzz/pkg-1.0", buf);
	linkage_add_pkg(map, "fuzz/other-2.0", buf);
	lp = linkage_get(map, "fuzz/pkg-1.0");
	if (lp != NULL && array_cnt(lp->objs) > 0) {
		linkage_obj *lo = array_get(lp->objs, 0);
		array       *cons;

		linkage_provided(map, lo->cat, lo->soname, "fuzz/pkg-1.0");
		cons = linkage_revdeps(map, NULL, lo->soname, NULL);
		array_deepfree(cons, free);
		if (array_cnt(lo->needed) > 0) {
			cons = linkage_revdeps(map, lo->cat,
									 array_get(lo->needed, 0), NULL);
			array_deepfree(cons, free);
		}
	}
	linkage_free(map);
	free(buf);
	return 0;
}
