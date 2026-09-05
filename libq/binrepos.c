/*
 * Copyright 2026-     Jaeger Hofer <antiq.hofer@gmail.com
 * Distributed under the terms of the GNU General Public License v2
 */

#include "main.h"

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>

#include "rmspace.h"
#include "binrepos.h"

void
binrepos_parse(FILE *fp, binrepos_parse_cb *cb, void *ctx)
{
	char   *line = NULL;
	size_t  len  = 0;
	char    name[128]        = "";
	char    uri[_Q_PATH_MAX] = "";
	char    loc[_Q_PATH_MAX] = "";
	char    gbex[4096]       = "";
	char    gbin[4096]       = "";
	char    keypkg[256]      = "";
	int     priority         = 1;
	int     verify_sig       = -1;
	int     frozen           = 0;
	bool    insection        = false;

	while (getline(&line, &len, fp) != -1) {
		char *s = rmspace(line);
		char *e;

		if (*s == '\0' || *s == '#' || *s == ';')
			continue;

		if (*s == '[') {
			if (insection)
				cb(ctx, name, uri, loc, priority, verify_sig,
				   frozen, gbex, gbin, keypkg);
			e = strchr(s, ']');
			if (e == NULL)
				continue;
			*e = '\0';
			snprintf(name, sizeof(name), "%s", s + 1);
			uri[0]     = '\0';
			loc[0]     = '\0';
			gbex[0]    = '\0';
			gbin[0]    = '\0';
			keypkg[0]  = '\0';
			priority   = 1;
			verify_sig = -1;
			frozen     = 0;
			insection  = true;
			continue;
		}

		if (!insection)
			continue;

		e = strchr(s, '=');
		if (e == NULL)
			continue;
		*e = '\0';
		rmspace(s);
		e = rmspace(e + 1);

		if (strcmp(s, "sync-uri") == 0)
			snprintf(uri, sizeof(uri), "%s", e);
		else if (strcmp(s, "priority") == 0)
			priority = atoi(e);
		else if (strcmp(s, "location") == 0)
			snprintf(loc, sizeof(loc), "%s", e);
		else if (strcmp(s, "verify-signature") == 0)
			verify_sig = strcasecmp(e, "true") == 0 ||
						 strcasecmp(e, "yes") == 0 ||
						 strcmp(e, "1") == 0 ? 1 : 0;
		else if (strcmp(s, "frozen") == 0)
			frozen = strcasecmp(e, "true") == 0 ||
					 strcasecmp(e, "yes") == 0 ||
					 strcmp(e, "1") == 0 ? 1 : 0;
		else if (strcmp(s, "getbinpkg-exclude") == 0)
			snprintf(gbex, sizeof(gbex), "%s", e);
		else if (strcmp(s, "getbinpkg-include") == 0)
			snprintf(gbin, sizeof(gbin), "%s", e);
		else if (strcmp(s, "openpgp-key-package") == 0)
			snprintf(keypkg, sizeof(keypkg), "%s", e);
	}

	if (insection)
		cb(ctx, name, uri, loc, priority, verify_sig,
		   frozen, gbex, gbin, keypkg);

	free(line);
}