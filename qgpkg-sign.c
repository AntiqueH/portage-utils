/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  	   - <antiq.hofer@gmail.com>
 *
 * qgpkg-sign: a C reimplementation of portage's gpkg-sign
 * this is called THE SIGNER, the applet.
 * while gpgsign.c and gpgsign.h are exposed libs
 */

#include "main.h"
#include "applets.h"

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>
#include <xalloc.h>

#ifdef ENABLE_GPKG
# include <archive.h>
# include <archive_entry.h>
#endif

#include "array.h"
#include "gpgsign.h"
#include "gpkg.h"
#include "hash.h"
#include "set.h"
#include "xasprintf.h"

#define QGPKG_SIGN_FLAGS "kus" COMMON_FLAGS
static struct option const qgpkg_sign_long_opts[] = {
	{"keep-current-signature", no_argument, NULL, 'k'},
	{"allow-unsigned",         no_argument, NULL, 'u'},
	{"skip-signed",            no_argument, NULL, 's'},
	COMMON_LONG_OPTS
};
static const char * const qgpkg_sign_opts_help[] = {
	"Keep existing signature when updating signature",
	"Allow signing from unsigned packages when binpkg-request-signature is enabled",
	"Skip signing if a package is already signed",
	COMMON_OPTS_HELP
};
#define qgpkg_sign_usage(ret) usage(ret, QGPKG_SIGN_FLAGS, \
		qgpkg_sign_long_opts, qgpkg_sign_opts_help, NULL, \
		lookup_applet_idx("qgpkg-sign"))

#ifdef ENABLE_GPKG


static void
qgs_append(char **buf, size_t *len, size_t *cap,
		const char *data, size_t n)
{
	if (*len + n + 1 > *cap) {
		*cap = (*cap == 0 ? 4096 : *cap * 2);
		while (*len + n + 1 > *cap)
			*cap *= 2;
		*buf = xrealloc(*buf, *cap);
	}
	memcpy(*buf + *len, data, n);
	*len += n;
	(*buf)[*len] = '\0';
}

struct qgs_ent {
	char      *path;
	char      *base;
	long long  size;
	bool       sig;
};

struct qgs_scan {
	array *ents;
	array *members;
	char  *manifest;
	size_t manifest_len;
	size_t manifest_cap;
	char  *prefix;
	int    fmt;
	bool   sig_exist;
};

struct qgs_rd {
	struct archive *a;
};

static size_t
qgs_read_cb(char *dest, size_t destlen, void *ctx)
{
	struct qgs_rd *r = ctx;
	la_ssize_t     n = archive_read_data(r->a, dest, destlen);
	return n < 0 ? 0 : (size_t)n;
}

static void
qgs_scan_free(struct qgs_scan *sc)
{
	size_t          i;
	struct qgs_ent *en;
	struct gpkg_member *m;

	array_for_each(sc->ents, i, en) {
		free(en->path);
		free(en->base);
		free(en);
	}
	array_free(sc->ents);
	array_for_each(sc->members, i, m) {
		free(m->base);
		free(m);
	}
	array_free(sc->members);
	free(sc->manifest);
	free(sc->prefix);
}

static bool
qgs_scan(const char *gpkg_file, struct qgs_scan *sc, bool *format_bad)
{
	struct archive       *a;
	struct archive_entry *e;
	set                  *seen = create_set();
	bool                  ok   = true;
	bool                  first = true;

	memset(sc, 0, sizeof(*sc));
	sc->ents = array_new();
	sc->members = array_new();
	*format_bad = false;

	a = archive_read_new();
	qarchive_read_taronly(a);
	if (archive_read_open_filename(a, gpkg_file, BUFSIZ) != ARCHIVE_OK) {
		archive_read_free(a);
		free_set(seen);
		*format_bad = true;
		return false;
	}

	while (archive_read_next_header(a, &e) == ARCHIVE_OK) {
		const char *nm = archive_entry_pathname(e);
		const char *base;
		size_t      blen;

		if (first) {
			sc->fmt = archive_format(a);
			first = false;
		}

		if (nm == NULL ||
				!gpkg_member_ok(nm,
					archive_entry_filetype(e) == AE_IFREG,
					&sc->prefix, seen, gpkg_file)) {
			ok = false;
			*format_bad = true;
			break;
		}

		base = strrchr(nm, '/');
		base = base != NULL ? base + 1 : nm;
		blen = strlen(base);

		if (strcmp(base, "Manifest") == 0) {
			char       buf[BUFSIZ];
			la_ssize_t n;
			while ((n = archive_read_data(a, buf, sizeof(buf))) > 0)
				qgs_append(&sc->manifest, &sc->manifest_len,
						&sc->manifest_cap, buf, (size_t)n);
		} else {
			struct qgs_ent     *en = xzalloc(sizeof(*en));
			struct gpkg_member *m  = xzalloc(sizeof(*m));
			struct qgs_rd       rd = { a };
			size_t              flen = 0;

			en->path = xstrdup(nm);
			en->base = xstrdup(base);
			en->size = (long long)archive_entry_size(e);
			en->sig  = blen >= 4 && strcmp(base + blen - 4, ".sig") == 0;
			if (en->sig)
				sc->sig_exist = true;
			array_append(sc->ents, en);

			m->base = xstrdup(base);
			m->size = en->size;
			hash_multiple_cb(qgs_read_cb, &rd, NULL, NULL, NULL,
					m->sha512, m->blake2b, &flen,
					HASH_BLAKE2B | HASH_SHA512);
			array_append(sc->members, m);
		}
	}
	archive_read_free(a);
	free_set(seen);

	if (ok && sc->manifest != NULL &&
			strstr(sc->manifest, "-----BEGIN PGP SIGNATURE-----") != NULL)
		sc->sig_exist = true;

	return ok;
}

static char *
qgs_old_line(const char *manifest, const char *base)
{
	const char *p = manifest;
	const char *e;
	char       *line;
	char       *tok;
	char       *sp;
	char       *chk;

	while (p != NULL && *p != '\0') {
		size_t ll;

		e = strchr(p, '\n');
		ll = e != NULL ? (size_t)(e - p) : strlen(p);
		line = xmalloc(ll + 1);
		memcpy(line, p, ll);
		line[ll] = '\0';
		if (strncmp(line, "DATA ", 5) == 0) {
			chk = xstrdup(line);
			tok = strtok_r(chk, " \t", &sp);
			tok = strtok_r(NULL, " \t", &sp);
			if (tok != NULL && strcmp(tok, base) == 0) {
				free(chk);
				return line;
			}
			free(chk);
		}
		free(line);
		p = e != NULL ? e + 1 : NULL;
	}
	return NULL;
}

static char *
qgs_data_line(const char *base, const char *data, size_t len)
{
	char  sha512[SHA512_DIGEST_LENGTH + 1];
	char *line;
#ifdef HAVE_BLAKE2B
	char  blake2b[BLAKE2B_DIGEST_LENGTH + 1];
	char *h;

	h = hash_string(data, (ssize_t)len, HASH_BLAKE2B);
	snprintf(blake2b, sizeof(blake2b), "%s", h != NULL ? h : "");
	h = hash_string(data, (ssize_t)len, HASH_SHA512);
	snprintf(sha512, sizeof(sha512), "%s", h != NULL ? h : "");
	xasprintf(&line, "DATA %s %zu BLAKE2B %s SHA512 %s",
			base, len, blake2b, sha512);
#else
	char *h;

	h = hash_string(data, (ssize_t)len, HASH_SHA512);
	snprintf(sha512, sizeof(sha512), "%s", h != NULL ? h : "");
	xasprintf(&line, "DATA %s %zu SHA512 %s", base, len, sha512);
#endif
	return line;
}

static bool
qgs_ent_by_base(struct qgs_scan *sc, const char *base)
{
	size_t          i;
	struct qgs_ent *en;

	array_for_each(sc->ents, i, en)
		if (strcmp(en->base, base) == 0)
			return true;
	return false;
}

static int
qgs_write_member(struct archive *aw, const char *path,
		const char *data, size_t len)
{
	struct archive_entry *e = archive_entry_new();
	int                   r = 0;

	archive_entry_set_pathname(e, path);
	archive_entry_set_size(e, (la_int64_t)len);
	archive_entry_set_filetype(e, AE_IFREG);
	archive_entry_set_perm(e, 0644);
	archive_entry_set_mtime(e, time(NULL), 0);
	if (archive_write_header(aw, e) != ARCHIVE_OK)
		r = -1;
	else if (len > 0 &&
			archive_write_data(aw, data, len) != (la_ssize_t)len)
		r = -1;
	archive_entry_free(e);
	return r;
}

static int
qgs_update_signature(const char *gpkg_file, struct qgs_scan *sc,
		bool keep_current)
{
	struct archive       *ar;
	struct archive       *aw;
	struct archive_entry *e;
	array                *lines = array_new();
	char                 *tmp;
	char                 *sig     = NULL;
	size_t                siglen  = 0;
	char                 *line;
	char                 *mnf     = NULL;
	size_t                mnflen  = 0;
	size_t                mnfcap  = 0;
	size_t                i;
	int                   fd;
	int                   ret     = -1;
	char                  buf[BUFSIZ * 8];
	la_ssize_t            n;

	xasprintf(&tmp, "%s.XXXXXX", gpkg_file);
	fd = mkstemp(tmp);
	if (fd == -1) {
		free(tmp);
		array_free(lines);
		return -1;
	}
	fchmod(fd, 0644);

	aw = archive_write_new();
	switch (sc->fmt) {
	case ARCHIVE_FORMAT_TAR_GNUTAR:
		archive_write_set_format_gnutar(aw);
		break;
	case ARCHIVE_FORMAT_TAR_PAX_INTERCHANGE:
		archive_write_set_format_pax(aw);
		break;
	default:
		archive_write_set_format_ustar(aw);
		break;
	}
	if (archive_write_open_fd(aw, fd) != ARCHIVE_OK)
		goto out;

	xasprintf(&line, "%s/gpkg-1", sc->prefix);
	if (qgs_write_member(aw, line, NULL, 0) != 0) {
		free(line);
		goto out;
	}
	free(line);
	array_append(lines, qgs_data_line("gpkg-1", "", 0));

	ar = archive_read_new();
	qarchive_read_taronly(ar);
	if (archive_read_open_filename(ar, gpkg_file, BUFSIZ) != ARCHIVE_OK) {
		archive_read_free(ar);
		goto out;
	}

	while (archive_read_next_header(ar, &e) == ARCHIVE_OK) {
		const char *nm = archive_entry_pathname(e);
		const char *base;
		size_t      blen;
		char       *sigbase;
		bool        fresh;

		base = strrchr(nm, '/');
		base = base != NULL ? base + 1 : nm;
		blen = strlen(base);

		if (strcmp(base, "gpkg-1") == 0 ||
				strcmp(base, "Manifest") == 0) {
			archive_read_data_skip(ar);
			continue;
		}

		if (blen >= 4 && strcmp(base + blen - 4, ".sig") == 0) {
			if (!keep_current) {
				archive_read_data_skip(ar);
				continue;
			}
			line = qgs_old_line(sc->manifest, base);
			if (line == NULL) {
				archive_read_data_skip(ar);
				continue;
			}
			array_append(lines, line);
			{
				struct archive_entry *ce = archive_entry_clone(e);
				if (archive_write_header(aw, ce) != ARCHIVE_OK) {
					archive_entry_free(ce);
					archive_read_free(ar);
					goto out;
				}
				archive_entry_free(ce);
			}
			while ((n = archive_read_data(ar, buf, sizeof(buf))) > 0)
				if (archive_write_data(aw, buf, (size_t)n) != n) {
					archive_read_free(ar);
					goto out;
				}
			continue;
		}

		line = qgs_old_line(sc->manifest, base);
		if (line == NULL) {
			archive_read_free(ar);
			goto out;
		}
		array_append(lines, line);

		xasprintf(&sigbase, "%s.sig", base);
		fresh = !(keep_current && qgs_ent_by_base(sc, sigbase));

		{
			struct archive_entry *ce = archive_entry_clone(e);
			struct gpgsign        g;

			if (archive_write_header(aw, ce) != ARCHIVE_OK) {
				archive_entry_free(ce);
				free(sigbase);
				archive_read_free(ar);
				goto out;
			}
			archive_entry_free(ce);

			if (fresh && gpgsign_start(true, &g) != 0) {
				free(sigbase);
				archive_read_free(ar);
				goto out;
			}
			while ((n = archive_read_data(ar, buf, sizeof(buf))) > 0) {
				if (archive_write_data(aw, buf, (size_t)n) != n ||
						(fresh &&
						 gpgsign_feed(&g, buf, (size_t)n) != 0)) {
					if (fresh)
						gpgsign_abort(&g);
					free(sigbase);
					archive_read_free(ar);
					goto out;
				}
			}
			if (fresh) {
				char *sigpath;

				if (gpgsign_finish(&g, &sig, &siglen) != 0) {
					free(sigbase);
					archive_read_free(ar);
					goto out;
				}
				xasprintf(&sigpath, "%s.sig", nm);
				if (qgs_write_member(aw, sigpath, sig, siglen) != 0) {
					free(sigpath);
					free(sig);
					sig = NULL;
					free(sigbase);
					archive_read_free(ar);
					goto out;
				}
				free(sigpath);
				array_append(lines, qgs_data_line(sigbase, sig, siglen));
				free(sig);
				sig = NULL;
			}
		}
		free(sigbase);
	}
	archive_read_free(ar);

	array_for_each(lines, i, line) {
		qgs_append(&mnf, &mnflen, &mnfcap, line, strlen(line));
		qgs_append(&mnf, &mnflen, &mnfcap, "\n", 1);
	}

	if (gpgsign_buf(mnf != NULL ? mnf : "", mnflen, false,
				&sig, &siglen) != 0)
		goto out;

	xasprintf(&line, "%s/Manifest", sc->prefix);
	if (qgs_write_member(aw, line, sig, siglen) != 0) {
		free(line);
		goto out;
	}
	free(line);
	free(sig);
	sig = NULL;

	if (archive_write_close(aw) != ARCHIVE_OK)
		goto out;
	archive_write_free(aw);
	aw = NULL;
	if (rename(tmp, gpkg_file) != 0)
		goto out;
	ret = 0;

out:
	if (aw != NULL) {
		archive_write_close(aw);
		archive_write_free(aw);
	}
	close(fd);
	if (ret != 0)
		unlink(tmp);
	free(tmp);
	free(sig);
	free(mnf);
	array_for_each(lines, i, line)
		free(line);
	array_free(lines);
	return ret;
}

#endif

int qgpkg_sign_main(int argc, char **argv)
{
	int         i;
	bool        keep_current   = false;
	bool        allow_unsigned = false;
	bool        skip_signed    = false;
	const char *gpkg_file;

	while ((i = GETOPT_LONG(QGPKG_SIGN, qgpkg_sign, "")) != -1) {
		switch (i) {
		COMMON_GETOPTS_CASES(qgpkg_sign)
		case 'k': keep_current   = true; break;
		case 'u': allow_unsigned = true; break;
		case 's': skip_signed    = true; break;
		}
	}
	if (optind >= argc) {
		warn("no gpkg package file specified");
		qgpkg_sign_usage(EXIT_FAILURE);
	}
	gpkg_file = argv[optind];

#ifndef ENABLE_GPKG
	(void)keep_current;
	(void)allow_unsigned;
	(void)skip_signed;
	(void)gpkg_file;
	warn("gpkg support not compiled in");
	return EXIT_FAILURE;
#else
	{
		struct stat     st;
		struct qgs_scan sc;
		bool            format_bad;
		bool            request;

		if (!gpgsign_vars_ok())
			return EXIT_FAILURE;
		if (stat(gpkg_file, &st) != 0 || !S_ISREG(st.st_mode)) {
			warn("File not found: %s", gpkg_file);
			return EXIT_FAILURE;
		}

		if (!qgs_scan(gpkg_file, &sc, &format_bad)) {
			qgs_scan_free(&sc);
			warn("Invalid binary package format: %s", gpkg_file);
			return EXIT_FAILURE;
		}

		if (skip_signed && sc.sig_exist) {
			printf(" %s*%s %s already signed, skipping.\n",
					GREEN, NORM, gpkg_file);
			qgs_scan_free(&sc);
			return EXIT_SUCCESS;
		}

		request = set_get(features, "binpkg-request-signature") != NULL;
		if (allow_unsigned)
			request = false;

		if (sc.manifest == NULL ||
				(!sc.sig_exist && request)) {
			qgs_scan_free(&sc);
			warn("Signature exception: %s", gpkg_file);
			return EXIT_FAILURE;
		}

		if (!gpkg_manifest_verify(sc.manifest, sc.members, gpkg_file)) {
			qgs_scan_free(&sc);
			warn("Signature exception: %s", gpkg_file);
			return EXIT_FAILURE;
		}

		if (sc.sig_exist && !qm_gpkg_verify(gpkg_file)) {
			qgs_scan_free(&sc);
			warn("Signature exception: %s", gpkg_file);
			return EXIT_FAILURE;
		}

		if (qgs_update_signature(gpkg_file, &sc, keep_current) != 0) {
			qgs_scan_free(&sc);
			warn("Signature exception: %s", gpkg_file);
			return EXIT_FAILURE;
		}

		qgs_scan_free(&sc);
		printf(" %s*%s %s signed.\n", GREEN, NORM, gpkg_file);
		return EXIT_SUCCESS;
	}
#endif
}