/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * Standalone replay driver for the fuzz targets. Linked in place of
 * libFuzzer so that every fuzz_* target also builds as an ordinary check
 * program: it feeds each file under seeds/<target> and
 * regressions/<target> to LLVMFuzzerTestOneInput.
 */

#include <config.h>

#include <dirent.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#ifndef FUZZ_SRCDIR
# define FUZZ_SRCDIR "."
#endif

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);
int LLVMFuzzerInitialize(int *argc, char ***argv) __attribute__((weak));

static int
run_file(const char *path)
{
	FILE    *f;
	uint8_t *buf;
	long     len;
	size_t   got;

	f = fopen(path, "rb");
	if (f == NULL)
		return -1;

	if (fseek(f, 0, SEEK_END) != 0 || (len = ftell(f)) < 0 ||
		fseek(f, 0, SEEK_SET) != 0)
	{
		fclose(f);
		return -1;
	}

	buf = malloc((size_t)len + 1);
	if (buf == NULL) {
		fclose(f);
		return -1;
	}

	got = fread(buf, 1, (size_t)len, f);
	fclose(f);

	LLVMFuzzerTestOneInput(buf, got);
	free(buf);
	return 0;
}

static int
run_dir(const char *dir, size_t *count)
{
	DIR           *d;
	struct dirent *de;
	struct stat    st;
	char           path[4096];

	d = opendir(dir);
	if (d == NULL)
		return -1;

	while ((de = readdir(d)) != NULL) {
		if (de->d_name[0] == '.')
			continue;

		snprintf(path, sizeof(path), "%s/%s", dir, de->d_name);
		if (stat(path, &st) != 0 || !S_ISREG(st.st_mode))
			continue;

		printf("  %s\n", path);
		fflush(stdout);

		if (run_file(path) == 0)
			(*count)++;
	}

	closedir(d);
	return 0;
}

int
main(int argc, char **argv)
{
	const char *target;
	char        seeds[4096];
	char        regressions[4096];
	size_t      count = 0;
	int         found = 0;

	if (LLVMFuzzerInitialize != NULL)
		LLVMFuzzerInitialize(&argc, &argv);

	target = strrchr(argv[0], '/');
	target = target != NULL ? target + 1 : argv[0];
	if (strncmp(target, "fuzz_", 5) == 0)
		target += 5;

	snprintf(seeds, sizeof(seeds), FUZZ_SRCDIR "/seeds/%s", target);
	snprintf(regressions, sizeof(regressions),
			 FUZZ_SRCDIR "/regressions/%s", target);

	if (run_dir(seeds, &count) == 0)
		found = 1;
	if (run_dir(regressions, &count) == 0)
		found = 1;

	if (!found) {
		fprintf(stderr, "%s: no corpus under %s\n", argv[0], seeds);
		return 77;
	}

	printf("%s: %zu inputs replayed\n", target, count);
	return 0;
}
