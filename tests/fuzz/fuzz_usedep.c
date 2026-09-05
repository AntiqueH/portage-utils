/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 * 
 * Fuzz the [..]-style USE-dependency evaluator (libq/usedep.c):
 * - The dep strings come from a remote Packages index (a binpkg's DEPEND/
 * RDEPEND fields), so they are attacker-influenced.
 * - The usedep chain and the conditional/default forms must not read out of bounds.
 *
 * Input: up to four newline-separated fields:
 *   atom-with-usedeps \n USE \n IUSE \n parent-USE
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "atom.h"
#include "set.h"
#include "usedep.h"

const char *argv0 = "fuzz_usedep";
FILE *warnout;

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char        *buf;
	char        *lines[4] = { NULL, NULL, NULL, NULL };
	char        *p;
	char        *sp;
	int          n = 0;
	atom_ctx    *a;
	set_t       *use;
	set_t       *iuse;
	set_t       *puse;

	if (size == 0 || size > 4096)
		return 0;
	if (warnout == NULL)
		warnout = fopen("/dev/null", "w");

	buf = malloc(size + 1);
	if (buf == NULL)
		return 0;
	memcpy(buf, data, size);
	buf[size] = '\0';

	for (p = strtok_r(buf, "\n", &sp);
		 p != NULL && n < 4;
		 p = strtok_r(NULL, "\n", &sp))
		lines[n++] = p;

	if (lines[0] == NULL) {
		free(buf);
		return 0;
	}

	a    = atom_explode(lines[0]);
	use  = usedep_flags_to_set(lines[1]);
	iuse = usedep_flags_to_set(lines[2]);
	puse = lines[3] != NULL ? usedep_flags_to_set(lines[3]) : NULL;

	if (a != NULL) {
		const atom_usedep *ud;

		for (ud = a->usedeps; ud != NULL; ud = ud->next)
			(void)usedep_ok(ud, use, iuse, puse);
		atom_implode(a);
	}

	free_set(use);
	free_set(iuse);
	if (puse != NULL)
		free_set(puse);
	free(buf);
	return 0;
}
