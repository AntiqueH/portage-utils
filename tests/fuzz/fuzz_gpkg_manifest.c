/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * Fuzz the GLEP 74 Manifest verifier used on every gpkg (GLEP 78) binary
 * package. The Manifest text is attacker-controlled when the container is
 * served by a binhost; gpkg_manifest_verify() parses the DATA lines' size and
 * digest fields by hand and cross-checks them against the members. 
 * - ^We feed it raw bytes against a small fixed member set so mutations can reach the size
 * and digest comparison paths.
 */
#include "main.h"
#include "gpkg.h"
#include "array.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <xalloc.h>

const char *argv0 = "fuzz_gpkg_manifest";
FILE *warnout;

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int
LLVMFuzzerInitialize(int *argc, char ***argv)
{
	(void)argc;
	(void)argv;
	warnout = fopen("/dev/null", "we");
	if (warnout == NULL)
		warnout = stderr;
	return 0;
}

static struct gpkg_member *
mk_member(const char *base, long long size, const char *sha512,
		const char *blake2b)
{
	struct gpkg_member *m = xzalloc(sizeof(*m));
	m->base = xstrdup(base);
	m->size = size;
	snprintf(m->sha512, sizeof(m->sha512), "%s", sha512);
	snprintf(m->blake2b, sizeof(m->blake2b), "%s", blake2b);
	return m;
}

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char               *s;
	array              *members;
	size_t              i;
	struct gpkg_member *m;

	if (size > 65536)
		return 0;
	s = malloc(size + 1);
	if (s == NULL)
		return 0;
	memcpy(s, data, size);
	s[size] = '\0';

	members = array_new();
	array_append(members, mk_member("gpkg-1", 0,
		"cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
		"47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
		"786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419"
		"d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"));
	array_append(members, mk_member("metadata.tar.zst", 0, "", ""));
	array_append(members, mk_member("image.tar.zst", 0, "", ""));

	gpkg_manifest_verify(s, members, "fuzz");

	array_for_each(members, i, m) {
		free(m->base);
		free(m);
	}
	array_free(members);
	free(s);
	return 0;
}
