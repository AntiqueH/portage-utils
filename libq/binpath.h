/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 */

#ifndef BINPATH_H
#define BINPATH_H 1

#include <stdbool.h>
#include <stddef.h>

/* If name ends in a known binpkg extension (.gpkg.tar/.tbz2/.xpak),
 * return name with *outlen set to the length before the extension;
 * otherwise NULL. */
/* A binpkg index PATH (e.g. "cat/pn/pf-BUILDID.gpkg.tar" or a flat
 * "cat/pf.tbz2") reduced to a malloc'd "cat/pf" with the build id
 * stripped, or NULL when it is not a valid binary package name. The
 * input is attacker-influenced (it comes from a remote Packages
 * index), so this must reject rather than misbehave on junk. */

const char *binpath_strip_ext(const char *name, size_t *outlen);


bool binpath_version_like(const char *s);

bool binpath_digits(const char *s);


char *binpath_rel_cpv(const char *rel);

#endif