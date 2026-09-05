/*
 * Copyright 2026-     Jaeger Hofer <antiq.hofer@gmail.com>
 * Distributed under the terms of the GNU General Public License v2
 */

#ifndef _BINREPOS_H
#define _BINREPOS_H 1

#include <stdio.h>

typedef void (binrepos_parse_cb)(void *ctx, const char *name,
		const char *uri, const char *loc, int priority,
		int verify_sig, int frozen, const char *gbex,
		const char *gbin, const char *keypkg);

void binrepos_parse(FILE *fp, binrepos_parse_cb *cb, void *ctx);

#endif