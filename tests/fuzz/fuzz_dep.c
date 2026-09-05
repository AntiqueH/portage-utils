/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

#include <config.h>

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "set.h"
#include "array.h"
#include "atom.h"
#include "dep.h"

const char *argv0 = "fuzz_dep";
FILE *warnout;

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int
LLVMFuzzerInitialize(int *argc, char ***argv)
{
	(void)argc;
	(void)argv;
	warnout = fopen("/dev/null", "we");
	if (warnout == NULL)
		warnout = stderr;
	return 0;
}

int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	char        *s;
	dep_node_t  *t;
	set_t       *use;
	array       *flat;

	if (size == 0 || size > 8192)
		return 0;
	s = malloc(size + 1);
	if (s == NULL)
		return 0;
	memcpy(s, data, size);
	s[size] = '\0';

	t = dep_grow_tree(s);
	if (t != NULL) {
		dep_print_tree(warnout, t, 0, NULL, NULL, 1);
		(void)dep_node_atom(t);
		(void)dep_node_type(t);
		(void)dep_node_children(t);
		use = create_set();
		add_set("foo", use);
		add_set("abi_x86_64", use);
		dep_prune_use(t, use);
		flat = dep_flatten_tree(t);
		if (flat != NULL)
			array_free(flat);
		dep_burn_tree(t);
		free_set(use);
	}

	free(s);
	return 0;
}
