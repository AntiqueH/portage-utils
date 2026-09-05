/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.        - <antiq.hofer@gmail.com>
 *
 * Reconstruct a "cat/pf" from a binary package index PATH, factored
 * out of qmerge so it can be fuzzed on its own: the PATH strings come
 * from a remote Packages index and are therefore untrusted.
 * Semantics mirror portage's bintree _populate_local.
 */

#include "main.h"

#include <ctype.h>
#include <stdbool.h>
#include <string.h>

#include "atom.h"
#include "xasprintf.h"
#include "binpath.h"

const char *
binpath_strip_ext(const char *name, size_t *outlen)
{
	static const char * const exts[] = { ".gpkg.tar", ".tbz2", ".xpak" };
	size_t len = strlen(name);
	size_t i;

	for (i = 0; i < ARRAY_SIZE(exts); i++) {
		size_t el = strlen(exts[i]);

		if (len > el && strcmp(name + len - el, exts[i]) == 0) {
			*outlen = len - el;
			return name;
		}
	}
	return NULL;
}

bool
binpath_version_like(const char *s)
{
	if (!isdigit((unsigned char)*s))
		return false;
	while (isdigit((unsigned char)*s))
		s++;
	while (*s == '.' && isdigit((unsigned char)s[1])) {
		s++;
		while (isdigit((unsigned char)*s))
			s++;
	}
	if (isalpha((unsigned char)*s))
		s++;
	while (*s == '_') {
		static const char * const sf[] =
			{ "alpha", "beta", "pre", "rc", "p" };
		size_t k;
		bool   m = false;

		s++;
		for (k = 0; k < ARRAY_SIZE(sf); k++) {
			size_t sl = strlen(sf[k]);

			if (strncmp(s, sf[k], sl) == 0) {
				s += sl;
				m = true;
				break;
			}
		}
		if (!m)
			return false;
		while (isdigit((unsigned char)*s))
			s++;
	}
	if (s[0] == '-' && s[1] == 'r' && isdigit((unsigned char)s[2])) {
		s += 3;
		while (isdigit((unsigned char)*s))
			s++;
	}
	return *s == '\0';
}

bool
binpath_digits(const char *s)
{
	if (*s == '\0')
		return false;
	for (; *s != '\0'; s++)
		if (!isdigit((unsigned char)*s))
			return false;
	return true;
}

char *
binpath_rel_cpv(const char *rel)
{
	const char *base  = strrchr(rel, '/');
	const char *slash = strchr(rel, '/');
	bool        subdir;
	size_t      blen;
	char        name[_Q_PATH_MAX];
	char       *dash;
	char       *cpv;
	atom_ctx   *a;
	bool        ok = false;

	if (base == NULL || slash == NULL)
		return NULL;
	subdir = base != slash;
	base++;
	if (binpath_strip_ext(base, &blen) == NULL || blen >= sizeof(name))
		return NULL;
	memcpy(name, base, blen);
	name[blen] = '\0';
	if (subdir) {
		dash = strrchr(name, '-');
		if (dash != NULL && binpath_digits(dash + 1))
			*dash = '\0';
	}

	{
		const char *p;

		for (p = name; *p != '\0'; p++)
			if (!(isalnum((int)(unsigned char)*p) ||
					*p == '+' || *p == '_' || *p == '.' || *p == '-'))
				return NULL;
		for (p = rel; p < slash; p++)
			if (!(isalnum((int)(unsigned char)*p) ||
					*p == '+' || *p == '_' || *p == '.' || *p == '-'))
				return NULL;
	}

	xasprintf(&cpv, "%.*s/%s", (int)(slash - rel), rel, name);
	a = atom_explode(cpv);
	if (a != NULL) {
		ok = a->PN != NULL && a->PV != NULL && a->PV[0] != '\0';
		if (ok) {
			dash = strrchr(a->PN, '-');
			if (dash != NULL && binpath_version_like(dash + 1))
				ok = false;
		}
		atom_implode(a);
	}
	if (!ok) {
		free(cpv);
		return NULL;
	}
	return cpv;
}