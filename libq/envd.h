/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 */

#ifndef ENVD_H
#define ENVD_H 1

#include "array.h"
#include "set.h"

/* Plans for envd.h!
 * one KEY=value pair parsed from an /etc/env.d file */
/* array_deepfree callback for an array of struct envd_kv */
/* parse one env.d file into an array of struct envd_kv: KEY=value
 * lines, optional leading "export ", surrounding matched quotes
 * stripped, comment/blank lines skipped, no $-expansion. Returns a
 * malloc'd array (caller frees with envd_file_free), or NULL when the
 * file cannot be read. */
/* non-comment, non-blank, whitespace-trimmed lines of a file as a
 * malloc'd array of char* (portage grabfile semantics) */
/* collect the ld.so(8) library search dirs named by an ld.so.conf
 * tree into *into, resolving includes via glob. Cycle-guarded
 * (visited set + depth cap) because these files are shipped
 * inside binary packages. */

struct envd_kv {
	char *k;
	char *v;
};


void envd_file_free(void *data);


array *envd_parse(const char *path);


array *envd_grabfile(const char *path);


void envd_read_ldsoconf(const char *root, const char *path, set **into);

#endif