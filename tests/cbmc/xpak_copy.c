/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * CBMC for the xpak entry-copy pattern tree_pkg_xpak_read_cb:
 * for any slice xpak_data_bounds_ok() authorizes, copying len bytes and
 * placing the NUL in the destination must never read data[size] or
 * beyond.
 */
#include "xpak.c"

int main(void)
{
	unsigned int coff, clen;
	char data[16];
	char copy[17];

	if (xpak_data_bounds_ok(coff, clen, sizeof(data))) {
		unsigned int i;

		__CPROVER_assume(clen <= sizeof(data));
		for (i = 0; i < clen; i++)
			copy[i] = data[coff + i];
		copy[clen] = '\0';
	}
	return 0;
}