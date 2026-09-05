/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.        - <antiq.hofer@gmail.com>
 */

#ifndef USEDEP_H
#define USEDEP_H 1

#include <stdbool.h>

#include "atom.h"
#include "set.h"

set_t *usedep_flags_to_set(const char *str);
bool   usedep_ok(const atom_usedep *ud, set_t *cuse, set_t *ciuse,
                 set_t *puse);

#endif
