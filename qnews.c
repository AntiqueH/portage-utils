/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  	   - <antiq.hofer@gmail.com>
 *
 * qnews: eselect news, except it is written in C, needs no eselect,
 * no portage and no repo, same three verbs, fewer opinions.
 */

#include "main.h"
#include "applets.h"

#include <dirent.h>
#include <ctype.h>
#include <sys/stat.h>
#include <xalloc.h>

#include "array.h"
#include "eat_file.h"
#include "rmspace.h"
#include "set.h"

#define QNEWS_FLAGS "" COMMON_FLAGS
static struct option const qnews_long_opts[] = {
	COMMON_LONG_OPTS
};
static const char * const qnews_opts_help[] = {
	COMMON_OPTS_HELP
};
#define qnews_usage(ret) usage(ret, QNEWS_FLAGS, qnews_long_opts, \
		qnews_opts_help, "list | count | read [all|<item> ...]", \
		lookup_applet_idx("qnews"))

static char qnews_dir[_Q_PATH_MAX];

static set *
qnews_load(const char *repoid, const char *suf)
{
	char    p[_Q_PATH_MAX + 64];
	char   *buf = NULL;
	size_t  len = 0;
	char   *line;
	char   *sp;
	set    *ids = create_set();

	snprintf(p, sizeof(p), "%s/news-%s.%s", qnews_dir, repoid, suf);
	if (eat_file(p, &buf, &len) && buf != NULL) {
		for (line = strtok_r(buf, "\r\n", &sp);
			 line != NULL;
			 line = strtok_r(NULL, "\r\n", &sp))
			if (line[0] != '\0')
				add_set(line, ids);
	}
	free(buf);
	return ids;
}

static void
qnews_store(const char *repoid, const char *suf, set *ids)
{
	char   p[_Q_PATH_MAX + 64];
	FILE  *f;
	array *keys;
	size_t n;
	char  *id;

	snprintf(p, sizeof(p), "%s/news-%s.%s", qnews_dir, repoid, suf);
	f = fopen(p, "w");
	if (f == NULL) {
		warnp("cannot write %s", p);
		return;
	}
	keys = set_keys(ids);
	array_for_each(keys, n, id)
		fprintf(f, "%s\n", id);
	array_free(keys);
	fclose(f);
	chmod(p, 0644);
}

static char *
qnews_body_path(const char *repoid, const char *nid)
{
	static char p[_Q_PATH_MAX + 512];
	size_t      o;

	snprintf(p, sizeof(p), "%s/items/%s/%s/%s.en.txt",
			 qnews_dir, repoid, nid, nid);
	if (access(p, R_OK) == 0)
		return p;
	for (o = 0; o < array_cnt(overlays); o++) {
		snprintf(p, sizeof(p), "%s/metadata/news/%s/%s.en.txt",
				 (char *)array_get(overlays, o), nid, nid);
		if (access(p, R_OK) == 0)
			return p;
	}
	return NULL;
}

static void
qnews_title(const char *repoid, const char *nid, char *out, size_t outlen)
{
	char   *path = qnews_body_path(repoid, nid);
	char   *buf  = NULL;
	size_t  len  = 0;
	char   *line;
	char   *sp;

	snprintf(out, outlen, "(no title)");
	if (path == NULL || !eat_file(path, &buf, &len) || buf == NULL) {
		free(buf);
		return;
	}
	for (line = strtok_r(buf, "\r\n", &sp);
		 line != NULL;
		 line = strtok_r(NULL, "\r\n", &sp))
	{
		if (line[0] == '\0')
			break;
		if (strncmp(line, "Title:", 6) == 0) {
			snprintf(out, outlen, "%s", rmspace(line + 6));
			break;
		}
	}
	free(buf);
}

static void
qnews_print_body(const char *repoid, const char *nid)
{
	char   *path = qnews_body_path(repoid, nid);
	char   *buf  = NULL;
	size_t  len  = 0;
	size_t  i;
	size_t  blen;

	if (path == NULL) {
		warn("no cached body for %s/%s", repoid, nid);
		return;
	}
	if (!eat_file(path, &buf, &len) || buf == NULL) {
		free(buf);
		return;
	}
	blen = strlen(buf);
	for (i = 0; i < blen; i++)
		if (buf[i] != '\n' && buf[i] != '\t' &&
				(unsigned char)buf[i] < 0x20)
			buf[i] = '?';
	printf("%s%s/%s%s\n\n%s\n", GREEN, repoid, nid, NORM, buf);
	free(buf);
}

static char *
qnews_dup(const char *s, size_t len)
{
	char *r = xmalloc(len + 1);

	memcpy(r, s, len);
	r[len] = '\0';
	return r;
}

static array *
qnews_repoids(void)
{
	DIR           *d;
	struct dirent *de;
	array         *ids = array_new();

	d = opendir(qnews_dir);
	if (d == NULL)
		return ids;
	while ((de = readdir(d)) != NULL) {
		size_t L = strlen(de->d_name);

		if (strncmp(de->d_name, "news-", 5) != 0)
			continue;
		if (L > 5 + 7 && strcmp(de->d_name + L - 7, ".unread") == 0)
			array_append(ids, qnews_dup(de->d_name + 5, L - 5 - 7));
		else if (L > 5 + 5 && strcmp(de->d_name + L - 5, ".read") == 0)
			array_append(ids, qnews_dup(de->d_name + 5, L - 5 - 5));
	}
	closedir(d);
	return ids;
}

static int
qnews_list(bool count_only)
{
	array  *repos = qnews_repoids();
	set    *seen  = create_set();
	size_t  r;
	char   *repoid;
	int     unread_total = 0;

	array_for_each(repos, r, repoid) {
		set    *unread;
		set    *rd;
		array  *keys;
		size_t  n;
		char   *id;

		if (contains_set(repoid, seen) != NULL)
			continue;
		add_set(repoid, seen);
		unread = qnews_load(repoid, "unread");
		rd     = qnews_load(repoid, "read");
		unread_total += (int)cnt_set(unread);
		if (!count_only) {
			keys = set_keys(unread);
			array_for_each(keys, n, id) {
				char title[256];

				qnews_title(repoid, id, title, sizeof(title));
				printf("  [%sN%s] %s %s%s%s: %s\n", RED, NORM,
					   repoid, GREEN, id, NORM, title);
			}
			array_free(keys);
			keys = set_keys(rd);
			array_for_each(keys, n, id) {
				char title[256];

				qnews_title(repoid, id, title, sizeof(title));
				printf("  [ ] %s %s: %s\n", repoid, id, title);
			}
			array_free(keys);
		}
		free_set(unread);
		free_set(rd);
	}
	array_for_each(repos, r, repoid)
		free(repoid);
	array_free(repos);
	free_set(seen);
	if (count_only)
		printf("%d\n", unread_total);
	else if (unread_total == 0)
		qprintf("no unread news items\n");
	return EXIT_SUCCESS;
}

static int
qnews_read(int argc, char **argv)
{
	array  *repos = qnews_repoids();
	set    *seen  = create_set();
	size_t  r;
	char   *repoid;
	bool    all = argc > 0 && strcmp(argv[0], "all") == 0;

	array_for_each(repos, r, repoid) {
		set    *unread;
		set    *rd;
		array  *keys;
		size_t  n;
		char   *id;
		bool    dirty = false;

		if (contains_set(repoid, seen) != NULL)
			continue;
		add_set(repoid, seen);
		unread = qnews_load(repoid, "unread");
		rd     = qnews_load(repoid, "read");

		if (argc == 0 || all) {
			keys = set_keys(all ? rd : unread);
			if (all) {
				array  *ukeys = set_keys(unread);

				array_for_each(ukeys, n, id)
					array_append(keys, id);
				array_free(ukeys);
			}
			array_for_each(keys, n, id) {
				bool ign;

				qnews_print_body(repoid, id);
				if (contains_set(id, unread) != NULL) {
					add_set(id, rd);
					(void)del_set(id, unread, &ign);
					dirty = true;
				}
			}
			array_free(keys);
		} else {
			int a;

			for (a = 0; a < argc; a++) {
				bool ign;

				if (contains_set(argv[a], unread) == NULL &&
						contains_set(argv[a], rd) == NULL)
					continue;
				qnews_print_body(repoid, argv[a]);
				if (contains_set(argv[a], unread) != NULL) {
					add_set(argv[a], rd);
					(void)del_set(argv[a], unread, &ign);
					dirty = true;
				}
			}
		}
		if (dirty) {
			qnews_store(repoid, "unread", unread);
			qnews_store(repoid, "read", rd);
		}
		free_set(unread);
		free_set(rd);
	}
	array_for_each(repos, r, repoid)
		free(repoid);
	array_free(repos);
	free_set(seen);
	return EXIT_SUCCESS;
}

int qnews_main(int argc, char **argv)
{
	int ret;

	while ((ret = GETOPT_LONG(QNEWS, qnews, "")) != -1) {
		switch (ret) {
			COMMON_GETOPTS_CASES(qnews)
		}
	}

	snprintf(qnews_dir, sizeof(qnews_dir), "%svar/lib/gentoo/news",
			 portroot);

	if (optind == argc || strcmp(argv[optind], "list") == 0)
		return qnews_list(false);
	if (strcmp(argv[optind], "count") == 0)
		return qnews_list(true);
	if (strcmp(argv[optind], "read") == 0)
		return qnews_read(argc - optind - 1, argv + optind + 1);
	qnews_usage(EXIT_FAILURE);
	return EXIT_FAILURE;
}
