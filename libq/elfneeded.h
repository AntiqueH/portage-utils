/*
 * Copyright 2026-     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 *
 * Native reader for the dynamic-linking identity of an ELF object:
 * multilib category, DT_SONAME and the DT_NEEDED list, clone behavior
 * from scanelf via portage's LinkageMapELF for preserved libraries.
 */

#ifndef _ELFNEEDED_H
#define _ELFNEEDED_H 1

#include "array.h"

typedef struct elf_needed_ {
	char  *arch;
	char  *soname;
	array *needed;
} elf_needed;

elf_needed *elf_needed_read(const char *path);
void        elf_needed_free(elf_needed *en);

#endif