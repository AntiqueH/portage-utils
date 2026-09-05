/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 */

/* GnuPG signing .h briungs BINPKG_GPG_SIGNING_BASE_COMMAND with the
 * portage [PORTAGE_CONFIG] substitution and streams data through it.
 * detached=true yields an armored detached signature, false a clearsigned
 * document. Output is malloc'd into *out. */

#ifndef GPGSIGN_H
#define GPGSIGN_H 1

#include <stdbool.h>
#include <stddef.h>
#include <sys/types.h>

struct gpgsign {
	pid_t   pid;
	int     in;
	int     out;
	int     err;
	char   *obuf;
	size_t  olen;
	size_t  ocap;
	char   *ebuf;
	size_t  elen;
	size_t  ecap;
};

bool gpgsign_vars_ok(void);
int  gpgsign_start(bool detached, struct gpgsign *g);
int  gpgsign_feed(struct gpgsign *g, const char *data, size_t len);
int  gpgsign_finish(struct gpgsign *g, char **out, size_t *out_len);
void gpgsign_abort(struct gpgsign *g);
int  gpgsign_buf(const char *data, size_t len, bool detached,
		char **out, size_t *out_len);

#endif