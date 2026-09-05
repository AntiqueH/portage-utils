/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * Fuzz the native ELF dynamic-section reader (libq/elfneeded.c):
 * - The preserved-libs GC feeds it whatever bytes sit at registry paths
 * on disk, so headers, program headers, dynamic entries and the string
 * table must all be bounds-checked against hostile files.
 *
 * Input: raw file content handed to elf_needed_read via a temp file
 * under TMPDIR (the fuzz checks point it at tests/r/tmp) or the
 * current directory.
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "elfneeded.h"

const char *argv0 = "fuzz_elfneeded";
FILE *warnout;

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char        tmpl[4096];
	const char *td = getenv("TMPDIR");
	int         fd;
	elf_needed *en;

	if (warnout == NULL)
		warnout = stderr;
	if (size > 1 << 20)
		return 0;

	snprintf(tmpl, sizeof(tmpl), "%s/fuzz_elfneeded.XXXXXX",
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

	en = elf_needed_read(tmpl);
	elf_needed_free(en);

	unlink(tmpl);
	return 0;
}