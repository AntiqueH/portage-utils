/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.        - <antiq.hofer@gmail.com>
 *
 * Parser for binhost/repo Moves (package-update) files, factored out
 * of qmerge so it can be fuzzed on its own: the buffer comes from a
 * remote binhost and is therefore untrusted.  Semantics mirror
 * portage's package-move instruction grammar.
 */

#include "main.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "atom.h"
#include "xalloc.h"
#include "xasprintf.h"
#include "moves.h"

void
moves_free(array *mv)
{
	size_t       i;
	struct move *m;

	if (mv == NULL)
		return;
	array_for_each(mv, i, m) {
		free(m->a1);
		free(m->a2);
		free(m->a3);
		free(m);
	}
	array_free(mv);
}

array *
moves_parse(const char *bufc)
{
	array *mv  = array_new();
	char  *tmp = xstrdup(bufc);
	char  *line;
	char  *lsp;

	for (line = strtok_r(tmp, "\r\n", &lsp);
		 line != NULL;
		 line = strtok_r(NULL, "\r\n", &lsp))
	{
		char *t1, *t2, *t3, *t4, *sp;

		if (line[0] == '#')
			continue;
		t1 = strtok_r(line, " \t", &sp);
		t2 = strtok_r(NULL, " \t", &sp);
		t3 = strtok_r(NULL, " \t", &sp);
		t4 = strtok_r(NULL, " \t", &sp);
		if (t1 == NULL)
			continue;
		if (strcmp(t1, "move") == 0 && t2 != NULL && t3 != NULL) {
			depend_atom *f = atom_explode(t2);
			depend_atom *g = atom_explode(t3);

			/* move endpoints aren't versioned, so we gotta be careful */
			if (f == NULL || g == NULL ||
					f->CATEGORY == NULL || f->PN == NULL || f->PV != NULL ||
					g->CATEGORY == NULL || g->PN == NULL || g->PV != NULL) {
				warn("Moves: malformed move instruction: %s %s",
					 t2 != NULL ? t2 : "?", t3 != NULL ? t3 : "?");
			} else {
				struct move *m = xzalloc(sizeof(*m));

				xasprintf(&m->a1, "%s/%s", f->CATEGORY, f->PN);
				xasprintf(&m->a2, "%s/%s", g->CATEGORY, g->PN);
				array_append(mv, m);
			}
			if (f != NULL)
				atom_implode(f);
			if (g != NULL)
				atom_implode(g);
		} else if (strcmp(t1, "slotmove") == 0 &&
				   t2 != NULL && t3 != NULL && t4 != NULL) {
			struct move *m = xzalloc(sizeof(*m));

			m->slotmove = true;
			m->a1 = xstrdup(t2);
			m->a2 = xstrdup(t3);
			m->a3 = xstrdup(t4);
			array_append(mv, m);
		} else {
			warn("Moves: unrecognised instruction: %s", t1);
		}
	}
	free(tmp);
	return mv;
}