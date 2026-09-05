/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "contents.h"

const char *argv0 = "fuzz_contents";
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
	char *line;
	char *sp;

	if (size == 0 || size > 65536)
		return 0;
	s = malloc(size + 1);
	if (s == NULL)
		return 0;
	memcpy(s, data, size);
	s[size] = '\0';

	for (line = strtok_r(s, "\n", &sp);
	     line != NULL;
	     line = strtok_r(NULL, "\n", &sp))
	{
		contents_entry *e = contents_parse_line(line);

		if (e != NULL && e->name != NULL)
			(void)strlen(e->name);
	}

	free(s);
	return 0;
}
