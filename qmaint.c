/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  	   - <antiq.hofer@gmail.com>
 *
 * qmaint: package management housekeeping, a C port of emaint.
 * Modules mirror their emaint namesakes.
 */

#include "main.h"
#include "applets.h"

#include <stdbool.h>
#include <string.h>

#define QMAINT_FLAGS "cf" COMMON_FLAGS
static struct option const qmaint_long_opts[] = {
	{"check",       no_argument, NULL, 'c'},
	{"fix",         no_argument, NULL, 'f'},
	{"no-ldconfig", no_argument, NULL, 128},
	{"delete-individual-files", no_argument, NULL, 129},
	{"remove",      no_argument, NULL, 130},
	COMMON_LONG_OPTS
};
static const char * const qmaint_opts_help[] = {
	"Check for problems",
	"Fix problems",
	"env module: do not regenerate ld.so.cache",
	"vdb module, with --fix: remove the per-field files after writing the metadata file",
	"vdb module: restore per-field files and remove the metadata file (undo --fix)",
	COMMON_OPTS_HELP
};
#define qmaint_usage(ret) usage(ret, QMAINT_FLAGS, qmaint_long_opts, \
		qmaint_opts_help, NULL, lookup_applet_idx("qmaint"))

int qmaint_main(int argc, char **argv)
{
	int  i;
	bool check       = false;
	bool fix         = false;
	bool no_ldconfig = false;
	bool del_indiv   = false;
	bool remove_meta = false;

	while ((i = GETOPT_LONG(QMAINT, qmaint, "")) != -1) {
		switch (i) {
		case 'c': check       = true; break;
		case 'f': fix         = true; break;
		case 128: no_ldconfig = true; break;
		case 129: del_indiv   = true; break;
		case 130: remove_meta = true; break;
		COMMON_GETOPTS_CASES(qmaint)
		}
	}

	if (optind + 1 != argc)
		qmaint_usage(EXIT_FAILURE);
	if (check && fix) {
		warn("--check and --fix are exclusive options");
		return EXIT_FAILURE;
	}
	if (!check && !fix)
		check = true;
	if (no_ldconfig && strcmp(argv[optind], "env") != 0) {
		warn("--no-ldconfig only applies to the env module");
		return EXIT_FAILURE;
	}
	if ((del_indiv || remove_meta) && strcmp(argv[optind], "vdb") != 0) {
		warn("--delete-individual-files and --remove only apply to "
			 "the vdb module");
		return EXIT_FAILURE;
	}
	if (remove_meta && fix) {
		warn("--fix and --remove are exclusive options");
		return EXIT_FAILURE;
	}
	if (del_indiv && !fix) {
		warn("--delete-individual-files requires --fix");
		return EXIT_FAILURE;
	}

	if (strcmp(argv[optind], "binhost") == 0)
		return qmerge_binhost_maint(fix);
	if (strcmp(argv[optind], "moves") == 0)
		return qmerge_moves_maint(fix);
	if (strcmp(argv[optind], "news") == 0)
		return qmerge_news_maint(fix);
	if (strcmp(argv[optind], "env") == 0)
		return qmerge_env_maint(fix, no_ldconfig);
	if (strcmp(argv[optind], "vdb") == 0)
		return qmerge_vdb_maint(fix, del_indiv, remove_meta);

	warn("unknown module '%s' (available: binhost, moves, news, env, vdb)",
		 argv[optind]);
	return EXIT_FAILURE;
}