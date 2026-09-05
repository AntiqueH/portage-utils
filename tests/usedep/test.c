/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 * 
 * Separated test for non-standardized make.confs, PYTHON_TARGETS..
 */

#include "main.h"

#include <stdio.h>

#include "atom.h"
#include "set.h"
#include "usedep.h"

const char *argv0;
FILE *warnout;

int main(int argc, char *argv[])
{
	int   fails = 0;
	set  *use;
	set  *iuse;
	struct { const char *desc; const char *dep; const char *use;
			 const char *iuse; const char *puse; bool want; } cases[] = {
		/* plain [flag] */
		{ "[a] with a on",        "c/p[a]",    "a b",  "a b",  NULL, true  },
		{ "[a] with a off",       "c/p[a]",    "b",    "a b",  NULL, false },
		{ "[-a] with a off",      "c/p[-a]",   "b",    "a b",  NULL, true  },
		{ "[-a] with a on",       "c/p[-a]",   "a",    "a b",  NULL, false },
		/* (+)/(-) defaults for flag absent from IUSE */
		{ "[a(+)] a not in IUSE", "c/p[a(+)]", "b",    "b",    NULL, true  },
		{ "[a(-)] a not in IUSE", "c/p[a(-)]", "b",    "b",    NULL, false },
		{ "[a] a not in IUSE",    "c/p[a]",    "b",    "b",    NULL, false },
		{ "[a,-b] both ok",       "c/p[a,-b]", "a",    "a b",  NULL, true  },
		{ "[a,-b] b on -> fail",  "c/p[a,-b]", "a b",  "a b",  NULL, false },
		{ "py314(+) enabled",  "d/r[python_targets_python3_14(+)]",
		  "python_targets_python3_14", "python_targets_python3_14", NULL, true },
		{ "py314(+) missing -> fail (in IUSE, off)",
		  "d/r[python_targets_python3_14(+)]",
		  "python_targets_python3_12", "python_targets_python3_12 python_targets_python3_14",
		  NULL, false },
		/* parent-conditional = */
		{ "[a=] parent on cand on",  "c/p[a=]", "a", "a", "a", true  },
		{ "[a=] parent on cand off", "c/p[a=]", "b", "a b", "a", false },
		{ "[!a=] parent on cand off","c/p[!a=]","b", "a b", "a", true  },
	};
	size_t i;

	(void)argc;
	argv0 = argv[0];
	warnout = stderr;

	for (i = 0; i < ARRAY_SIZE(cases); i++) {
		atom_ctx *dep = atom_explode(cases[i].dep);
		bool      got;
		set      *pu  = cases[i].puse != NULL ?
						usedep_flags_to_set(cases[i].puse) : NULL;
		bool      ok  = true;
		const atom_usedep *ud;

		use  = usedep_flags_to_set(cases[i].use);
		iuse = usedep_flags_to_set(cases[i].iuse);
		for (ud = dep->usedeps; ud != NULL; ud = ud->next)
			if (!usedep_ok(ud, use, iuse, pu)) {
				ok = false;
				break;
			}
		got = ok;
		printf("%s %-40s (want=%d got=%d)\n",
			   got == cases[i].want ? "PASS" : "FAIL",
			   cases[i].desc, cases[i].want, got);
		if (got != cases[i].want)
			fails++;
		free_set(use);
		free_set(iuse);
		if (pu != NULL)
			free_set(pu);
		atom_implode(dep);
	}
	printf("usedep: %d failure(s)\n", fails);
	return fails;
}
