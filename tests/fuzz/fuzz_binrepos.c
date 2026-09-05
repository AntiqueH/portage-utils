/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * Fuzz the binrepos.conf parser (libq/binrepos.c)
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include "binrepos.h"

const char *argv0 = "fuzz_binrepos";
FILE *warnout;

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

static void
count_cb(void *ctx, const char *name, const char *uri, const char *loc,
		 int priority, int verify_sig, int frozen, const char *gbex,
		 const char *gbin, const char *keypkg)
{
	size_t *n = ctx;

	(void)priority;
	(void)verify_sig;
	(void)frozen;
	*n += strlen(name) + strlen(uri) + strlen(loc) +
		  strlen(gbex) + strlen(gbin) + strlen(keypkg);
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
	FILE   *f;
	size_t  n = 0;

	f = fmemopen((void *)data, size, "r");
	if (f == NULL)
		return 0;
	binrepos_parse(f, count_cb, &n);
	fclose(f);
	return 0;
}