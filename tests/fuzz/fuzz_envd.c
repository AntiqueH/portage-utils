/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * Fuzz the /etc/env.d and ld.so.conf parsers (libq/envd.c). 
 * - Their input ships inside binary packages, so it is attacker-influenced.
 * - The ld.so.conf include walk in particular must survive cyclic and
 * deeply-nested include trees without recursing off the stack.
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "set.h"
#include "array.h"
#include "envd.h"

const char *argv0 = "fuzz_envd";
FILE *warnout;

static char fdir[4096];
static char fpath[4096];

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

static void
envd_fuzz_cleanup(void)
{
	unlink(fpath);
	rmdir(fdir);
}

int
LLVMFuzzerInitialize(int *argc, char ***argv)
{
	char tmpl[] = "/tmp/qfuzzenvdXXXXXX";

	(void)argc;
	(void)argv;
	warnout = fopen("/dev/null", "we");
	if (warnout == NULL)
		warnout = stderr;
	if (mkdtemp(tmpl) == NULL)
		exit(1);
	snprintf(fdir, sizeof(fdir), "%s", tmpl);
	snprintf(fpath, sizeof(fpath), "%s/f", fdir);
	atexit(envd_fuzz_cleanup);
	return 0;
}

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	FILE  *f;
	array *kvs;
	array *lines;
	set   *into;

	if (size > 65536)
		return 0;

	f = fopen(fpath, "we");
	if (f == NULL)
		return 0;
	if (size > 0)
		fwrite(data, 1, size, f);
	fclose(f);

	kvs = envd_parse(fpath);
	if (kvs != NULL)
		envd_file_free(kvs);

	lines = envd_grabfile(fpath);
	array_deepfree(lines, free);

	into = create_set();
	envd_read_ldsoconf(fdir, fpath, &into);
	free_set(into);

	unlink(fpath);
	return 0;
}