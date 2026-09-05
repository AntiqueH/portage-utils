/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * differential fuzz of libq/hash.c hash_multiple_cb.
 * - The serial single-digest path and the multi-digest path must produce identical
 * digests for identical input regardless of how the read callback
 * - chunks the data and flen must always equal the input length.
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "hash.h"

const char *argv0 = "fuzz_hash";
FILE *warnout;

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

struct feed {
	const uint8_t *data;
	size_t         len;
	size_t         pos;
	size_t         chunk;
};

static size_t
feed_cb(char *dest, size_t destlen, void *ctx)
{
	struct feed *f = ctx;
	size_t n = f->len - f->pos;

	if (n == 0)
		return 0;
	if (n > f->chunk)
		n = f->chunk;
	if (n > destlen)
		n = destlen;
	memcpy(dest, f->data + f->pos, n);
	f->pos += n;
	return n;
}

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
	char md5_a[34];
	char md5_b[34];
	char md5_c[34];
	char sha1_b[42];
	char sha256_b[66];
	char sha512_b[130];
	char blak2b_b[130];
	size_t flen;
	struct feed f;

	f = (struct feed){ data, size, 0, size ? size : 1 };
	flen = (size_t)-1;
	if (hash_multiple_cb(feed_cb, &f, md5_a, NULL, NULL, NULL, NULL,
						 &flen, HASH_MD5) != 0)
		abort();
	if (flen != size)
		abort();

	/* multi-digest path, same data */
	f = (struct feed){ data, size, 0, size ? size : 1 };
	flen = (size_t)-1;
	if (hash_multiple_cb(feed_cb, &f, md5_b, sha1_b, sha256_b, sha512_b,
						 blak2b_b, &flen,
						 HASH_MD5 | HASH_SHA1 | HASH_SHA256 |
						 HASH_SHA512 | HASH_BLAKE2B) != 0)
		abort();
	if (flen != size)
		abort();
	if (strcmp(md5_a, md5_b) != 0)
		abort();

	/* single-digest again, adversarial chunking from the input */
	f = (struct feed){ data, size, 0,
					   size ? (size % 7) + 1 : 1 };
	flen = (size_t)-1;
	if (hash_multiple_cb(feed_cb, &f, md5_c, NULL, NULL, NULL, NULL,
						 &flen, HASH_MD5) != 0)
		abort();
	if (flen != size)
		abort();
	if (strcmp(md5_a, md5_c) != 0)
		abort();

	return 0;
}