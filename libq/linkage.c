/*
 * Copyright 2026-     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 * 
 * Linkage implementation. This library will check all the linkage
 * in all packages .so files. Purpose is to maintain functioning packages.
 * This is portage regular action when it checks the preservation of libs
 * based on linkage.
 */

#include "main.h"

#include <stdlib.h>
#include <string.h>

#include <xalloc.h>

#include "set.h"
#include "array.h"
#include "linkage.h"

struct linkage_map_ {
	array *pkgs;
};

static void
linkage_obj_free(void *o)
{
	linkage_obj *lo = o;

	if (lo == NULL)
		return;
	free(lo->cat);
	free(lo->path);
	free(lo->soname);
	array_deepfree(lo->needed, free);
	array_deepfree(lo->rpath, free);
	free(lo);
}

static void
linkage_pkg_free(void *p)
{
	linkage_pkg *lp = p;

	if (lp == NULL)
		return;
	free(lp->cpv);
	array_deepfree(lp->objs, linkage_obj_free);
	free(lp);
}

linkage_map *
linkage_new(void)
{
	linkage_map *m = xzalloc(sizeof(*m));

	m->pkgs = array_new();
	return m;
}

static char *
linkage_strndup(const char *s, size_t len)
{
	char *ret = xmalloc(len + 1);

	memcpy(ret, s, len);
	ret[len] = '\0';
	return ret;
}

static void
linkage_split(array *out, const char *s, size_t len, char sep)
{
	const char *segs = s;
	const char *p    = s;
	const char *end  = s + len;

	while (p <= end) {
		if (p == end || *p == sep) {
			if (p > segs)
				array_append(out, linkage_strndup(segs, (size_t)(p - segs)));
			segs = p + 1;
		}
		p++;
	}
}

static linkage_obj *
linkage_parse_line(const char *line, size_t len)
{
	const char  *f[6];
	size_t       fl[6];
	size_t       nf   = 0;
	const char  *p    = line;
	const char  *end  = line + len;
	linkage_obj *lo;

	f[0]  = p;
	fl[0] = 0;
	while (p < end && nf < 6) {
		if (*p == ';') {
			fl[nf] = (size_t)(p - f[nf]);
			nf++;
			if (nf < 6)
				f[nf] = p + 1;
		}
		p++;
	}
	if (nf < 6) {
		fl[nf] = (size_t)(end - f[nf]);
		nf++;
	}
	if (nf < 5)
		return NULL;

	lo = xzalloc(sizeof(*lo));
	if (nf >= 6 && fl[5] > 0)
		lo->cat = linkage_strndup(f[5], fl[5]);
	else
		lo->cat = linkage_strndup(f[0], fl[0]);
	lo->path   = linkage_strndup(f[1], fl[1]);
	lo->soname = linkage_strndup(f[2], fl[2]);
	lo->needed = array_new();
	lo->rpath  = array_new();

	linkage_split(lo->needed, f[4], fl[4], ',');
	if (!(fl[3] == 5 && memcmp(f[3], "  -  ", 5) == 0))
		linkage_split(lo->rpath, f[3], fl[3], ':');
	return lo;
}

void
linkage_add_pkg(linkage_map *m, const char *cpv, const char *needed_txt)
{
	linkage_pkg *lp;
	const char  *p;
	const char  *ls;

	lp = xzalloc(sizeof(*lp));
	lp->cpv  = xstrdup(cpv);
	lp->objs = array_new();

	if (needed_txt != NULL) {
		ls = needed_txt;
		for (p = needed_txt; ; p++) {
			if (*p == '\n' || *p == '\0') {
				if (p > ls) {
					linkage_obj *lo =
							linkage_parse_line(ls, (size_t)(p - ls));

					if (lo != NULL)
						array_append(lp->objs, lo);
				}
				if (*p == '\0')
					break;
				ls = p + 1;
			}
		}
	}
	array_append(m->pkgs, lp);
}

linkage_pkg *
linkage_get(linkage_map *m, const char *cpv)
{
	size_t       i;
	linkage_pkg *lp;

	array_for_each(m->pkgs, i, lp)
		if (strcmp(lp->cpv, cpv) == 0)
			return lp;
	return NULL;
}

array *
linkage_pkgs(linkage_map *m)
{
	return m->pkgs;
}

bool
linkage_provided(linkage_map *m, const char *cat, const char *soname,
				 const char *exclude_cpv)
{
	size_t       i;
	size_t       n;
	linkage_pkg *lp;
	linkage_obj *lo;

	if (soname == NULL || *soname == '\0')
		return false;
	array_for_each(m->pkgs, i, lp) {
		if (exclude_cpv != NULL && strcmp(lp->cpv, exclude_cpv) == 0)
			continue;
		array_for_each(lp->objs, n, lo) {
			if (lo->soname[0] == '\0')
				continue;
			if (strcmp(lo->soname, soname) == 0 &&
					(cat == NULL || strcmp(lo->cat, cat) == 0))
				return true;
		}
	}
	return false;
}

array *
linkage_revdeps(linkage_map *m, const char *cat, const char *soname,
				  const char *exclude_cpv)
{
	array       *ret = array_new();
	set         *seen = create_set();
	size_t       i;
	size_t       n;
	size_t       k;
	linkage_pkg *lp;
	linkage_obj *lo;
	char        *nd;

	if (soname == NULL || *soname == '\0') {
		free_set(seen);
		return ret;
	}
	array_for_each(m->pkgs, i, lp) {
		if (exclude_cpv != NULL && strcmp(lp->cpv, exclude_cpv) == 0)
			continue;
		if (contains_set(lp->cpv, seen) != NULL)
			continue;
		array_for_each(lp->objs, n, lo) {
			bool hit = false;

			if (cat != NULL && strcmp(lo->cat, cat) != 0)
				continue;
			array_for_each(lo->needed, k, nd) {
				if (strcmp(nd, soname) == 0) {
					hit = true;
					break;
				}
			}
			if (hit) {
				add_set(lp->cpv, seen);
				array_append(ret, xstrdup(lp->cpv));
				break;
			}
		}
	}
	free_set(seen);
	return ret;
}

void
linkage_free(linkage_map *m)
{
	if (m == NULL)
		return;
	array_deepfree(m->pkgs, linkage_pkg_free);
	free(m);
}