/*
 * Copyright -2026     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 *
 * GLEP 74 Manifest entry line tokenizer: "<path> <size> <TYPE HASH ...>",
 * split out of qmanifest's verifier so the parse is fuzzable on its own.
 */

#ifndef _MFLINE_H
#define _MFLINE_H 1

typedef enum {
	MFLINE_OK = 0,
	MFLINE_END,
	MFLINE_NOPATH,
	MFLINE_NOSIZE,
	MFLINE_BADSIZE,
	MFLINE_NOHASH,
} mfline_err;

mfline_err mfline_split(char *line, char **path, char **size,
						long long *fsize, char **rest);
mfline_err mfline_next_hash(char **rest, char **type, char **hash);

#endif