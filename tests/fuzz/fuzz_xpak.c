/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * ffuzz the xpak parser (libq/xpak.c).
 * index scan field bounds, and the data-region entry copy the eaters
 * perform (the tree.c read-cb pattern, including the empty-last-entry
 * edge that held a 1-byte overread).
 */

#define _GNU_SOURCE

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include <sys/mman.h>

#include "xpak.h"

const char *argv0 = "fuzz_xpak";
FILE *warnout;

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

struct consume_state {
	size_t entries;
	size_t sink;
};

static void
consume_cb(void *ctx, char *pathname, int pathname_len,
		   int data_offset, int data_len, char *data)
{
	struct consume_state *cs = ctx;
	int i;

	cs->entries++;
	for (i = 0; i < pathname_len; i++)
		cs->sink += (unsigned char)pathname[i];

	if (data == NULL)
		return;

	while (data_len > 0 &&
		   isspace((int)data[data_offset + data_len - 1]))
		data_len--;
	{
		char *copy = malloc((size_t)data_len + 1);

		if (copy == NULL)
			return;
		memcpy(copy, data + data_offset, (size_t)data_len);
		copy[data_len] = '\0';
		cs->sink += strlen(copy);
		free(copy);
	}
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
	struct consume_state cs = { 0, 0 };
	int fd;
	ssize_t wr;

	fd = memfd_create("fuzz_xpak", 0);
	if (fd < 0)
		return 0;
	wr = write(fd, data, size);
	if (wr < 0 || (size_t)wr != size) {
		close(fd);
		return 0;
	}
	if (lseek(fd, 0, SEEK_SET) != 0) {
		close(fd);
		return 0;
	}


	(void)xpak_process_fd(fd, (size & 1) == 0, &cs, consume_cb);

	return 0;
}