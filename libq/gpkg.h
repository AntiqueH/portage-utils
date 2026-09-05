/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 */

/* Verify a GLEP 74 Manifest (text, attacker-controlled when the container
 * comes from a binhost) against the members hashed out of the container.
 * every DATA line's size and every listed supported digest must match, each
 * DATA line must name a present member, and every member must be listed.
 * gpkg_path is used only for diagnostics. Returns true iff consistent. */

#ifndef GPKG_H
#define GPKG_H 1

#include <stdbool.h>

#include "array.h"
#include "hash.h"
#include "set.h"

struct gpkg_member {
	char      *base;
	char       sha512[BLAKE2B_DIGEST_LENGTH + 1];
	char       blake2b[BLAKE2B_DIGEST_LENGTH + 1];
	long long  size;
	bool       verified;
};

bool gpkg_manifest_verify(const char *manifest, array *members,
		const char *gpkg_path);

/* Validate one GLEP 78 */
bool gpkg_member_ok(const char *name, bool is_regular, char **prefix,
		set *seen, const char *gpkg_path);

#endif