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

#include "atom.h"

const char *argv0 = "fuzz_atom";
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
	char      *s;
	char       buf[1024];
	atom_ctx  *a;
	atom_ctx  *b;
	atom_ctx  *c;

	if (size == 0 || size > 4096)
		return 0;
	s = malloc(size + 1);
	if (s == NULL)
		return 0;
	memcpy(s, data, size);
	s[size] = '\0';

	atom_compare_str(s, s);

	a = atom_explode(s);
	if (a != NULL) {
		char fbuf[1024];
		atom_to_string_r(buf, sizeof(buf), a);
		atom_format_r(fbuf, sizeof(fbuf), s, a);
		b = atom_explode(s);
		if (b != NULL) {
			atom_compare_flg(a, b, 0);
			atom_compare_flg(a, b,
					ATOM_COMP_NOSLOT | ATOM_COMP_NOSUBSLOT |
					ATOM_COMP_NOREPO);
			atom_implode(b);
		}
		c = atom_clone(a);
		if (c != NULL) {
			atom_compare_flg(a, c, 0);
			atom_implode(c);
		}
		atom_implode(a);
	}

	free(s);
	return 0;
}
