/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * Fuzz the binpkg index PATH -> cpv parser (libq/binpath.c).
 * - The PATH field is read verbatim from a remote Packages index, so it is
 *   attacker-influenced; binpath_rel_cpv must reject junk rather than
 *   read out of bounds or crash.
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "atom.h"
#include "binpath.h"

const char *argv0 = "fuzz_binpath";
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
	char   *s;
	char   *cpv;
	size_t  outlen;

	if (size > 8192)
		return 0;
	s = malloc(size + 1);
	if (s == NULL)
		return 0;
	memcpy(s, data, size);
	s[size] = '\0';

	(void)binpath_strip_ext(s, &outlen);
	(void)binpath_version_like(s);
	(void)binpath_digits(s);

	/* ... and the full PATH -> cpv reconstruction */
	cpv = binpath_rel_cpv(s);
	free(cpv);

	free(s);
	return 0;
}