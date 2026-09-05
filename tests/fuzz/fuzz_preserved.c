/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * Fuzz the preserved-libs registry JSON parser (libq/preserved.c):
 * - The registry file is root-written but may also come from a portage
 * of any vintage, so the parser must survive arbitrary bytes.
 * - String escapes, surrogate pairs, nesting depth and schema deviations
 * must not read out of bounds.
 *
 * Input: raw registry file content.
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "preserved.h"

const char *argv0 = "fuzz_preserved";
FILE *warnout;

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char           tmpl[4096];
	const char    *td = getenv("TMPDIR");
	int            fd;
	preserved_reg *reg;

	if (warnout == NULL)
		warnout = stderr;
	if (size > 1 << 20)
		return 0;

	snprintf(tmpl, sizeof(tmpl), "%s/fuzz_preserved.XXXXXX",
			 td != NULL && *td != '\0' ? td : ".");
	fd = mkstemp(tmpl);
	if (fd < 0)
		return 0;
	if (write(fd, data, size) < 0) {
		close(fd);
		unlink(tmpl);
		return 0;
	}
	close(fd);

	reg = preserved_open(tmpl);
	if (reg != NULL) {
		preserved_count(reg);
		preserved_store(reg);
		preserved_close(reg);
	}
	unlink(tmpl);
	return 0;
}
