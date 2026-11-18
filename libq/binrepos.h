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

struct binrepos_dflt
{
  char uri[4096];
  char loc[4096];
  char gbex[4096];
  char gbin[4096];
  char keypkg[256];
  int  priority;
  int  verify_sig;
  int  frozen;
};

void binrepos_dflt_init(struct binrepos_dflt *dflt);
void binrepos_parse(FILE *fp, const struct binrepos_dflt *dflt,
		binrepos_parse_cb *cb, void *ctx);

#endif