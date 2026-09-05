/*
 * Copyright 2026-     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 * 
 * Linkage library to check how linkage is happening.
 * What a basic definition :)
 */

#ifndef _LINKAGE_H
#define _LINKAGE_H 1

#include <stdbool.h>
#include <stddef.h>

#include "array.h"

typedef struct linkage_obj_ {
	char  *cat;
	char  *path;
	char  *soname;
	array *needed;
	array *rpath;
} linkage_obj;

typedef struct linkage_pkg_ {
	char  *cpv;
	array *objs;
} linkage_pkg;

typedef struct linkage_map_ linkage_map;

linkage_map *linkage_new(void);
void         linkage_add_pkg(linkage_map *m, const char *cpv,
							 const char *needed_txt);
linkage_pkg *linkage_get(linkage_map *m, const char *cpv);
array       *linkage_pkgs(linkage_map *m);
bool         linkage_provided(linkage_map *m, const char *cat,
							  const char *soname, const char *exclude_cpv);
array       *linkage_revdeps(linkage_map *m, const char *cat,
							   const char *soname, const char *exclude_cpv);
void         linkage_free(linkage_map *m);

#endif