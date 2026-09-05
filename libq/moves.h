/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 */

#ifndef MOVES_H
#define MOVES_H 1

#include <stdbool.h>

#include "array.h"

/* one parsed instruction from a binhost/repo Moves (package-update)
 * file. For a "move": a1/a2 are the malloc'd old/new "cat/pn", a3
 * unused. For a "slotmove": a1=cat/pn atom, a2=old slot, a3=new
 * slot, all malloc'd. */
/* parse a Moves file buffer into a malloc'd array of struct move.
 * The buffer comes from a remote binhost, so malformed / hostile
 * inputs are warned about and skipped. "move" endpoints must be 
 * bare cat/pn (unversioned); anything else is rejected.
 * Should return a (possibly empty) array, never NULL. */
struct move {
	bool  slotmove;
	char *a1;
	char *a2;
	char *a3;
};

void moves_free(array *mv);


array *moves_parse(const char *bufc);

#endif