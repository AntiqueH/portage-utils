/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.        - <antiq.hofer@gmail.com>
 *
 * [..]-style USE-dependency evaluation
 */

#include "main.h"

#include <string.h>
#include <xalloc.h>

#include "atom.h"
#include "set.h"
#include "usedep.h"

set_t *
usedep_flags_to_set(const char *str)
{
	set  *s = create_set();
	char *tmp;
	char *tok;
	char *sp;

	if (str == NULL)
		return s;
	tmp = xstrdup(str);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok != '\0')
			add_set_unique(tok, s, NULL);
	}
	free(tmp);
	return s;
}

/* evaluate one [..]-style USE-dep element against a candidate's USE/IUSE.
 * puse is the depending package's USE (for the ?/= conditional forms),
 * can be NULL at the resolution root.
 * we need a little more definitions here because I'm sure we didn't cover
 * everything important. ( @francoisb ) */
bool
usedep_ok(const atom_usedep *ud, set_t *cuse, set_t *ciuse, set_t *puse)
{
	const char *f       = ud->use;
	bool        in_use  = contains_set(f, cuse) != NULL;
	bool        in_iuse = contains_set(f, ciuse) != NULL;
	bool        eff;

	if (ud->sfx_cond == ATOM_UC_COND || ud->sfx_cond == ATOM_UC_EQUAL) {
		bool pon = puse != NULL && contains_set(f, puse) != NULL;
		bool neg = ud->pfx_cond == ATOM_UC_NOT;

		if (ud->sfx_cond == ATOM_UC_EQUAL)
			return neg ? (in_use != pon) : (in_use == pon);
		if (neg)
			return pon ? true : in_use;
		return pon ? in_use : true;
	}

	if (in_use)
		eff = true;
	else if (in_iuse)
		eff = false;
	else if (ud->sfx_cond == ATOM_UC_PREV_ENABLED)
		eff = true;
	else if (ud->sfx_cond == ATOM_UC_PREV_DISABLED)
		eff = false;
	else
		return false;

	return ud->pfx_cond == ATOM_UC_NEG ? !eff : eff;
}
