/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * Fuzz the GLEP 74 Manifest entry line tokenizer (libq/mfline.c):
 *
 * Input: one raw Manifest entry line (path size TYPE HASH ...).
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mfline.h"

const char *argv0 = "fuzz_mfline";
FILE *warnout;

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char      *s;
	char      *path;
	char      *fsz;
	char      *rest;
	char      *type;
	char      *hash;
	long long  fsize;

	if (warnout == NULL)
		warnout = stderr;
	if (size > 65536)
		return 0;
	s = malloc(size + 1);
	if (s == NULL)
		return 0;
	memcpy(s, data, size);
	s[size] = '\0';

	if (mfline_split(s, &path, &fsz, &fsize, &rest) == MFLINE_OK) {
		for (;;) {
			mfline_err me = mfline_next_hash(&rest, &type, &hash);

			if (me != MFLINE_OK)
				break;
			if (strlen(type) > size || strlen(hash) > size)
				abort();
		}
	}

	free(s);
	return 0;
}