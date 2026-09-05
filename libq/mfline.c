/*
 * Copyright -2026     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 *
 * In-place tokenizer for one GLEP 74 Manifest entry line, the
 * split qmanifest's verify_file performed inline before.
 */

#include "main.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>

#include "mfline.h"

mfline_err
mfline_split(char *line, char **path, char **size,
			 long long *fsize, char **rest)
{
	char *p;
	char *sizeend;

	*path = line;
	p = strchr(*path, ' ');
	if (p == NULL)
		return MFLINE_NOPATH;
	*p++ = '\0';

	*size = p;
	p = strchr(*size, ' ');
	if (p == NULL)
		return MFLINE_NOSIZE;
	*p++ = '\0';

	errno = 0;
	*fsize = strtoll(*size, &sizeend, 10);
	if (sizeend == *size || *sizeend != '\0' ||
			errno == ERANGE || *fsize < 0)
		return MFLINE_BADSIZE;

	*rest = p;
	return MFLINE_OK;
}

mfline_err
mfline_next_hash(char **rest, char **type, char **hash)
{
	char *p;

	if (*rest == NULL || **rest == '\0')
		return MFLINE_END;

	*type = *rest;
	p = strchr(*type, ' ');
	if (p == NULL)
		return MFLINE_NOHASH;
	*p++ = '\0';

	*hash = p;
	p = strchr(*hash, ' ');
	if (p != NULL)
		*p++ = '\0';
	*rest = p;
	return MFLINE_OK;
}