/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * Fuzz the GLEP 78 member-layout validator. A malicious binhost
 * controls the member names inside a gpkg, so gpkg_member_ok() will guard
 * against absolute paths, path traversal, extra directory levels, duplicate
 * (same-name attack) members, and prefix-directory smuggling.
 * - So we feed the raw bytes as newline-separated member names 
 * against a fresh layout state.
 * - Hopefully this will stop monsters from invading the code.
 */
#include "main.h"
#include "gpkg.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

const char *argv0 = "fuzz_gpkg_structure";
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

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char *s;
	char *save;
	char *line;
	char *prefix = NULL;
	set  *seen;

	if (size > 65536)
		return 0;
	s = malloc(size + 1);
	if (s == NULL)
		return 0;
	memcpy(s, data, size);
	s[size] = '\0';

	seen = create_set();
	for (line = strtok_r(s, "\n", &save); line != NULL;
			line = strtok_r(NULL, "\n", &save)) {
		if (!gpkg_member_ok(line, true, &prefix, seen, "fuzz"))
			break;
	}

	free(prefix);
	free_set(seen);
	free(s);
	return 0;
}