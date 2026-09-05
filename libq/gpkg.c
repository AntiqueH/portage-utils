/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 */

#include "main.h"
#include "gpkg.h"

#include <stdlib.h>
#include <string.h>
#include <xalloc.h>

bool
gpkg_member_ok(const char *name, bool is_regular, char **prefix,
		set *seen, const char *gpkg_path)
{
	const char *slash;
	size_t      dirlen;

	if (name == NULL || name[0] == '/') {
		warn("%s: member with absolute path", gpkg_path);
		return false;
	}
	slash = strchr(name, '/');
	if (slash == NULL || strchr(slash + 1, '/') != NULL) {
		warn("%s: member not at exactly one directory level: %s",
				gpkg_path, name);
		return false;
	}
	if (!is_regular) {
		warn("%s: non-regular member: %s", gpkg_path, name);
		return false;
	}
	if (contains_set(name, seen) != NULL) {
		warn("%s: duplicate member '%s' (possible same-name attack)",
				gpkg_path, name);
		return false;
	}
	add_set(name, seen);

	dirlen = (size_t)(slash - name);
	if (*prefix == NULL) {
		*prefix = xmalloc(dirlen + 1);
		memcpy(*prefix, name, dirlen);
		(*prefix)[dirlen] = '\0';
	} else if (strncmp(name, *prefix, dirlen) != 0 ||
			(*prefix)[dirlen] != '\0') {
		warn("%s: members do not share a single prefix directory",
				gpkg_path);
		return false;
	}
	return true;
}

bool
gpkg_manifest_verify(const char *manifest, array *members,
		const char *gpkg_path)
{
	bool                ok    = true;
	size_t              i;
	struct gpkg_member *m;
	char               *mcopy = xstrdup(manifest);
	char               *savep;
	char               *line;
	set                *mseen = create_set();

	for (line = strtok_r(mcopy, "\n", &savep);
			ok && line != NULL;
			line = strtok_r(NULL, "\n", &savep))
	{
		char                buf[BUFSIZ];
		char               *toks[24];
		int                 ntok = 0;
		char               *tok;
		char               *sp;
		struct gpkg_member *found = NULL;
		long long           msize;
		int                 k;
		int                 matched = 0;

		if (strncmp(line, "DATA ", 5) != 0)
			continue;
		snprintf(buf, sizeof(buf), "%s", line);
		for (tok = strtok_r(buf, " \t", &sp);
				tok != NULL && ntok < (int)(sizeof(toks) / sizeof(toks[0]));
				tok = strtok_r(NULL, " \t", &sp))
			toks[ntok++] = tok;
		if (ntok < 3)
			continue;

		if (contains_set(toks[1], mseen) != NULL) {
			warn("%s: duplicate Manifest entry '%s'", gpkg_path, toks[1]);
			ok = false; break;
		}
		add_set(toks[1], mseen);

		array_for_each(members, i, m)
			if (strcmp(m->base, toks[1]) == 0) { found = m; break; }
		if (found == NULL) {
			warn("%s: Manifest lists '%s' but it is missing from the "
					"package", gpkg_path, toks[1]);
			ok = false; break;
		}

		msize = strtoll(toks[2], NULL, 10);
		if (msize != found->size) {
			warn("%s: '%s' size mismatch vs Manifest", gpkg_path, toks[1]);
			ok = false; break;
		}

		for (k = 3; k + 1 < ntok; k += 2) {
			const char *hn = toks[k];
			const char *hv = toks[k + 1];
			if (strcmp(hn, "SHA512") == 0 && found->sha512[0] != '\0') {
				if (strcasecmp(hv, found->sha512) != 0) {
					warn("%s: '%s' SHA512 mismatch vs Manifest",
							gpkg_path, toks[1]);
					ok = false; break;
				}
				matched++;
			} else if (strcmp(hn, "BLAKE2B") == 0 &&
					found->blake2b[0] != '\0') {
				if (strcasecmp(hv, found->blake2b) != 0) {
					warn("%s: '%s' BLAKE2B mismatch vs Manifest",
							gpkg_path, toks[1]);
					ok = false; break;
				}
				matched++;
			}
		}
		if (ok && matched < 1) {
			warn("%s: '%s' has no supported checksum in the Manifest",
					gpkg_path, toks[1]);
			ok = false; break;
		}
		if (ok)
			found->verified = true;
	}
	free(mcopy);
	free_set(mseen);

	if (ok) {
		array_for_each(members, i, m) {
			if (!m->verified) {
				warn("%s: '%s' is present but not listed in the Manifest",
						gpkg_path, m->base);
				ok = false;
				break;
			}
		}
	}
	return ok;
}
