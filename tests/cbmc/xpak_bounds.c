/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * CBMC proof for libq/xpak.c: xpak_data_bounds_ok() must never authorize
 * an out-of-bounds data slice. xpak (.tbz2/.xpak) is parsed straight from
 * a remote binhost, so (offset,len,size) are attacker-controlled 32-bit
 * fields. 
 * The eater reads x->data[offset .. offset+len) from a buffer
 * of exactly `size` bytes; we prove the check can only pass when that read
 * stays in bounds under non-wrapping arithmetic.
 *
 * Including the .c gives the proof the actual static function under test.
 */
#include "xpak.c"

int main(void)
{
	unsigned int offset, len, size;

	if (xpak_data_bounds_ok(offset, len, size)) {
		__CPROVER_assert(
				(unsigned long long)offset + (unsigned long long)len
					<= (unsigned long long)size,
				"xpak data slice within segment");
		__CPROVER_assert(offset <= size, "xpak offset within segment");
		__CPROVER_assert(len <= size, "xpak len within segment");
	}
	return 0;
}