/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.        - <antiq.hofer@gmail.com>
 *
 * /etc/env.d and ld.so.conf parsers, factored out of qmerge's
 * env-update so they can be safely fuzzed in isolation..
 */

#include "main.h"

#include <ctype.h>
#include <glob.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#include "xalloc.h"
#include "eat_file.h"
#include "envd.h"

void
envd_file_free(void *data)
{
	array          *kvs = data;
	size_t          i;
	struct envd_kv *kv;

	array_for_each(kvs, i, kv) {
		free(kv->k);
		free(kv->v);
		free(kv);
	}
	array_free(kvs);
}

array *
envd_parse(const char *path)
{
	char   *buf  = NULL;
	size_t  blen = 0;
	char   *line;
	char   *savep;
	array  *kvs;

	if (!eat_file(path, &buf, &blen)) {
		free(buf);
		return NULL;
	}

	kvs = array_new();
	for (line = strtok_r(buf, "\n", &savep);
		 line != NULL;
		 line = strtok_r(NULL, "\n", &savep))
	{
		char           *s = line;
		char           *eq;
		char           *v;
		size_t          vlen;
		struct envd_kv *kv;

		while (isspace((unsigned char)*s))
			s++;
		if (*s == '\0' || *s == '#')
			continue;
		if (strncmp(s, "export ", 7) == 0) {
			s += 7;
			while (isspace((unsigned char)*s))
				s++;
		}
		eq = strchr(s, '=');
		if (eq == NULL || eq == s)
			continue;
		*eq = '\0';
		v = eq + 1;
		vlen = strlen(v);
		while (vlen > 0 && isspace((unsigned char)v[vlen - 1]))
			v[--vlen] = '\0';
		if (vlen >= 2 &&
				((v[0] == '"'  && v[vlen - 1] == '"') ||
				 (v[0] == '\'' && v[vlen - 1] == '\'')))
		{
			v[vlen - 1] = '\0';
			v++;
		}
		kv = xmalloc(sizeof(*kv));
		kv->k = xstrdup(s);
		kv->v = xstrdup(v);
		array_append(kvs, kv);
	}
	free(buf);
	return kvs;
}

array *
envd_grabfile(const char *path)
{
	char   *buf  = NULL;
	size_t  blen = 0;
	char   *line;
	char   *savep;
	array  *ret  = array_new();

	if (!eat_file(path, &buf, &blen)) {
		free(buf);
		return ret;
	}
	for (line = strtok_r(buf, "\n", &savep);
		 line != NULL;
		 line = strtok_r(NULL, "\n", &savep))
	{
		char   *s = line;
		size_t  l;

		while (isspace((unsigned char)*s))
			s++;
		if (*s == '\0' || *s == '#')
			continue;
		l = strlen(s);
		while (l > 0 && isspace((unsigned char)s[l - 1]))
			s[--l] = '\0';
		array_append(ret, xstrdup(s));
	}
	free(buf);
	return ret;
}


/* seen holds the visited paths (cycle guard) and depth 
 * backstops pathological fan-out.
 * because a self- or mutually-including tree from a hostile binpkg
 * would otherwise recurse until the stack blows. */
static bool
envd_path_has_dotdot(const char *path)
{
	const char *p = path;

	while ((p = strstr(p, "..")) != NULL) {
		if ((p == path || p[-1] == '/') &&
				(p[2] == '\0' || p[2] == '/'))
			return true;
		p += 2;
	}
	return false;
}

static bool
envd_glob_sane(const char *pat)
{
	size_t      metasegs = 0;
	size_t      metas    = 0;
	bool        seg      = false;
	const char *p;

	for (p = pat; *p != '\0'; p++) {
		if (*p == '/') {
			seg = false;
			continue;
		}
		if (*p == '*' || *p == '?' || *p == '[') {
			metas++;
			if (!seg) {
				seg = true;
				metasegs++;
			}
		}
	}
	return metasegs <= 2 && metas <= 16;
}

static void
envd_read_ldsoconf_r(const char *root, const char *path, set **into,
		set *seen, int depth)
{
	array  *lines;
	size_t  i;
	char   *l;
	bool    added = false;
	struct stat pst;
	char   key[64];

	if (depth > 32)
		return;
	if (stat(path, &pst) == 0) {
		snprintf(key, sizeof(key), "%llu:%llu",
				 (unsigned long long)pst.st_dev,
				 (unsigned long long)pst.st_ino);
		add_set_unique(key, seen, &added);
	} else
		add_set_unique(path, seen, &added);
	if (!added)
		/* already visited on this walk: an include cycle, stop */
		return;

	lines = envd_grabfile(path);
	array_for_each(lines, i, l) {
		if (strncmp(l, "include", 7) == 0 &&
				isspace((unsigned char)l[7]))
		{
			char        pat[_Q_PATH_MAX];
			char       *p  = l + 8;
			const char *sl = strrchr(path, '/');
			glob_t  g;
			size_t  gi;

			while (isspace((unsigned char)*p))
				p++;
			if (*p == '/')
				snprintf(pat, sizeof(pat), "%s%s", root, p);
			else
				snprintf(pat, sizeof(pat), "%.*s/%s",
						 sl != NULL ?
						 (int)MIN((size_t)(sl - path), sizeof(pat) - 2) : 1,
						 path, p);
			if (envd_glob_sane(pat) &&
					glob(pat, GLOB_NOSORT, NULL, &g) == 0) {
				for (gi = 0; gi < g.gl_pathc; gi++) {
					struct stat st;

					if (envd_path_has_dotdot(g.gl_pathv[gi]))
						continue;

					/* an include glob (e.g. a hostile whole-root
					 * wildcard) can match directories and device or
					 * proc nodes; ld.so.conf includes are plain config
					 * files, so only recurse into regular ones */
					if (stat(g.gl_pathv[gi], &st) != 0 ||
							!S_ISREG(st.st_mode))
						continue;
					envd_read_ldsoconf_r(root, g.gl_pathv[gi], into,
										 seen, depth + 1);
				}
				globfree(&g);
			}
		} else {
			*into = add_set_unique(l, *into, NULL);
		}
	}
	array_deepfree(lines, free);
}

void
envd_read_ldsoconf(const char *root, const char *path, set **into)
{
	set *seen = create_set();

	envd_read_ldsoconf_r(root != NULL ? root : "", path, into, seen, 0);
	free_set(seen);
}