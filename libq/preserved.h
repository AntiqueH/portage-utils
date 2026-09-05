/*
 * Copyright 2026-     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 * 
 * Library for future component of preserved libs.
 * Basically the purpose would be to implement and understand how we can preserve
 * needed lbiraries for various packages.
 */

#ifndef _PRESERVED_H
#define _PRESERVED_H 1

#include <stdbool.h>
#include <stddef.h>

#include "array.h"

typedef struct preserved_entry_ {
	char  *cps;
	char  *cpv;
	char  *counter;
	array *paths;
} preserved_entry;

typedef struct preserved_reg_ preserved_reg;

preserved_reg *preserved_open(const char *file);
preserved_reg *preserved_open_ro(const char *file);
void   preserved_prune(preserved_reg *reg, const char *root);
void   preserved_register(preserved_reg *reg, const char *cpv,
						  const char *slot, const char *counter,
						  array *paths);
void   preserved_unregister(preserved_reg *reg, const char *cpv,
							const char *slot, const char *counter);
array *preserved_entries(preserved_reg *reg);
size_t preserved_count(preserved_reg *reg);
bool   preserved_store(preserved_reg *reg);
void   preserved_close(preserved_reg *reg);

#endif