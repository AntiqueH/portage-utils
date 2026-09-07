/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2005-2010 Ned Ludd		   - <solar@gentoo.org>
 * Copyright 2005-2014 Mike Frysinger  - <vapier@gentoo.org>
 * Copyright 2018-2026 Fabian Groffen  - <grobian@gentoo.org>
 * Copyright 2026-     Jaeger H.  	   - <antiq.hofer@gmail.com>
 */

#include "main.h"
#include "applets.h"

#include <stdio.h>
#include <string.h>
#include <fnmatch.h>
#include <dirent.h>
#include <ctype.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <xalloc.h>

#include <archive.h>
#include <archive_entry.h>

#include "array.h"
#include "atom.h"
#include "basename.h"
#include "contents.h"
#include "gpgsign.h"
#include "hash.h"
#include "human_readable.h"
#include "safe_io.h"
#include "scandirat.h"
#include "set.h"
#include "tree.h"
#include "xasprintf.h"
#include "xchdir.h"
#include "xmkdir.h"
#include "xpak.h"

#define QPKG_FLAGS "cEgxpP:" COMMON_FLAGS
static struct option const qpkg_long_opts[] = {
	{"clean",    no_argument, NULL, 'c'},
	{"eclean",   no_argument, NULL, 'E'},
	{"gpkg",     no_argument, NULL, 'g'},
	{"xpak",     no_argument, NULL, 'x'},
	{"pretend",  no_argument, NULL, 'p'},
	{"pkgdir",    a_argument, NULL, 'P'},
	COMMON_LONG_OPTS
};
static const char * const qpkg_opts_help[] = {
	"clean pkgdir of files that are not installed",
	"clean pkgdir of files that are not in the tree anymore",
	"force building of gpkg instead of BINPKG_FORMAT",
	"force building of tbz2/xpak instead of BINPKG_FORMAT",
	"pretend only",
	"alternate package directory",
	COMMON_OPTS_HELP
};
#define qpkg_usage(ret) usage(ret, QPKG_FLAGS, qpkg_long_opts, qpkg_opts_help, NULL, lookup_applet_idx("qpkg"))

extern char pretend;

typedef struct qpkg_cb_args {
	char     *bindir;
	tree_ctx *binpkg;
	tree_ctx *vdb;
	int       clean_notintree:1;
	int       build_gpkg:1;
	size_t    pkgs_made;
} qpkg_cb_args;

/* figure out what dirs we want to process for cleaning and display results. */
static int
qpkg_clean(qpkg_cb_args *args)
{
	size_t n;
	size_t disp_units = 0;
	uint64_t num_all_bytes = 0;
	array *bins;
	array *trees;
	tree_ctx *t;
	tree_ctx *pkgs;
	tree_pkg_ctx *binpkg;
	struct stat st;

	pkgs = args->binpkg;
	if (pkgs == NULL)
		return 1;

	bins  = tree_match_atom(pkgs, NULL, TREE_MATCH_DEFAULT);
	trees = array_new();

	if (args->clean_notintree) {
		const char *overlay;

		array_for_each(overlays, n, overlay) {
			t = tree_new(portroot, overlay, TREETYPE_EBUILD, true);
			if (t != NULL)
				array_append(trees, t);
		}
	} else {
		t = args->vdb;
		if (t != NULL)
			array_append(trees, t);
	}

	/* check which binpkgs exist in the trees (vdb or ebuilds), such
	 * that the remainder is what we would clean */
	array_for_each_rev(bins, n, binpkg) {
		size_t m;
		array_for_each(trees, m, t)
		{
			array *mx = tree_match_atom(t, tree_pkg_atom(binpkg, false),
									    (TREE_MATCH_DEFAULT |
									     TREE_MATCH_FIRST));
			size_t l  = array_cnt(mx);
			array_free(mx);

			if (l > 0)
			{
				array_remove(bins, n);
				break;
			}
		}
	}

	if (args->clean_notintree)
		array_deepfree(trees, tree_close_cb);
	else
		array_free(trees);
	trees = NULL;

	array_for_each(bins, n, binpkg) {
		array        *mx   = tree_match_atom(pkgs,
											 tree_pkg_atom(binpkg, false),
										 	 (TREE_MATCH_DEFAULT |
										  	  TREE_MATCH_FIRST));
		tree_pkg_ctx *pkg  = array_get(mx, 0);
		
		array_free(mx);

		if (pkg == NULL)
			continue;

		if (fstatat(tree_pkg_get_portroot_fd(pkg),
					tree_pkg_get_path(pkg),
					&st, AT_SYMLINK_NOFOLLOW) != -1)
		{
			if (S_ISREG(st.st_mode)) {
				disp_units = KILOBYTE;
				if ((st.st_size / KILOBYTE) > 1000)
					disp_units = MEGABYTE;
				num_all_bytes += st.st_size;
				qprintf(" %s[%s %3s %s %s]%s %s\n",
						DKBLUE, GREEN,
						make_human_readable_str(st.st_size, 1, disp_units),
						disp_units == MEGABYTE ? "MiB" : "KiB",
						DKBLUE, NORM, atom_format("%[CAT]/%[PF]%[BUILDID]",
												  tree_pkg_atom(pkg, false)));
			}
			if (!pretend)
				unlinkat(tree_pkg_get_portroot_fd(pkg),
						 tree_pkg_get_path(pkg), 0);
		}
	}

	array_free(bins);

	disp_units = KILOBYTE;
	if ((num_all_bytes / KILOBYTE) > 1000)
		disp_units = MEGABYTE;
	qprintf(" %s*%s Total space %sfreed in packages "
			"directory: %s%s %ciB%s\n", GREEN, NORM,
			pretend ? "that would be " : "", RED,
			make_human_readable_str(num_all_bytes, 1, disp_units),
			disp_units == MEGABYTE ? 'M' : 'K', NORM);

	return 0;
}

static int
check_pkg_install_mask(char *name)
{
	int i, iargc, ret;
	char **iargv;

	i = iargc = ret = 0;

	if (*name != '/')
		return ret;

	makeargv(pkg_install_mask, &iargc, &iargv);

	for (i = 1; i < iargc; i++) {
		if (fnmatch(iargv[i], name, 0) != 0)
			continue;
		ret = 1;
		break;
	}
	freeargv(iargc, iargv);
	return ret;
}

/* this is a simplified version of write_hadhes from qmanifest, maybe
 * one day consolidate the two? */
static char *
hashline_adv(char *p, char *end, int n)
{
	if (n < 0)
		return p;
	return (size_t)n < (size_t)(end - p) ? p + n : end;
}

static void
write_hashes
(
	const char *fname,
	const char *type,
	int         fd
)
{
	size_t flen = 0;
	char sha512[SHA512_DIGEST_LENGTH + 1];
	char blak2b[BLAKE2B_DIGEST_LENGTH + 1];
	char data[8192];
	size_t len;
	const char *name;

	name = strrchr(fname, '/');
	if (name != NULL)
		name++;
	else
		name = "";

	/* this is HASH_DEFAULT, but we still have to set the right buffers,
	 * so do it statically */
	sha512[0] = blak2b[0] = '\0';
	if (hash_compute_file(fname, NULL, sha512, blak2b, &flen,
					  HASH_SHA512 | HASH_BLAKE2B) != 0) {
		warnp("failed to hash %s", fname);
		return;
	}

	data[0] = '\0';
	{
		char *p = data;
		char *e = data + sizeof(data);
		p = hashline_adv(p, e, snprintf(p, e - p, "%s %s %zd",
					type, name, flen));
		p = hashline_adv(p, e, snprintf(p, e - p, " SHA512 %s", sha512));
		p = hashline_adv(p, e, snprintf(p, e - p, " BLAKE2B %s", blak2b));
		p = hashline_adv(p, e, snprintf(p, e - p, "\n"));
		len = (size_t)(p - data);
	}

	if (safe_write(fd, data, len) < 0)
		warnp("failed to write hash data");
}

#ifdef ENABLE_GPKG

/* support multiple compression formats, as per Portage requirements */
static const struct {
	const char *name;
	int       (*add)(struct archive *);
	const char *ext;
} qgpkg_codecs[] = {
	{ "zstd",  archive_write_add_filter_zstd,  ".zst" },
	{ "xz",    archive_write_add_filter_xz,    ".xz"  },
	{ "bzip2", archive_write_add_filter_bzip2, ".bz2" },
	{ "gzip",  archive_write_add_filter_gzip,  ".gz"  },
	{ "lz4",   archive_write_add_filter_lz4,   ".lz4" },
	{ "lzip",  archive_write_add_filter_lzip,  ".lz"  },
	{ "lzop",  archive_write_add_filter_lzop,  ".lzo" },
};

static void
qgpkg_compress_flags(struct archive *a, const char *codec)
{
	char        var[64];
	char       *flags;
	char       *tmp;
	char       *tok;
	char       *save;
	size_t      i;

	snprintf(var, sizeof(var), "BINPKG_COMPRESS_FLAGS_%s", codec);
	for (i = sizeof("BINPKG_COMPRESS_FLAGS_") - 1; var[i] != '\0'; i++)
		var[i] = (char)toupper((unsigned char)var[i]);
	flags = getenv(var);
	if (flags == NULL)
		flags = binpkg_compress_flags;
	if (flags == NULL || flags[0] == '\0')
		return;

	tmp = xstrdup(flags);
	for (tok = strtok_r(tmp, " \t", &save);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t", &save))
	{
		bool numeric = tok[0] == '-' && tok[1] != '\0';
		size_t n;

		for (n = 1; numeric && tok[n] != '\0'; n++)
			if (tok[n] < '0' || tok[n] > '9')
				numeric = false;
		if (numeric) {
			char opt[80];

			snprintf(opt, sizeof(opt), "%s:compression-level=%s",
					 codec, tok + 1);
			if (archive_write_set_options(a, opt) != ARCHIVE_OK)
				warn("BINPKG_COMPRESS_FLAGS: level '%s' not supported "
					 "for %s by the built-in packer, ignored", tok, codec);
		} else {
			warn("BINPKG_COMPRESS_FLAGS: '%s' not supported by the "
				 "built-in packer, ignored", tok);
		}
	}
	free(tmp);
}

static const char *
qgpkg_set_compression(struct archive *a)
{
	size_t i;

	if (binpkg_compress != NULL && binpkg_compress[0] != '\0') {
		if (strcmp(binpkg_compress, "none") == 0) {
			static bool warned = false;

			/* additional tests are required here
			 * there might actuallly be a issue with portage itself
			 * we did not hit this issue since our BINPKG_COMPRESS functions
			 * in regular parameters.
			 * maybe they will fix this one later, if proven correct? */
			if (!warned) {
				warn("BINPKG_COMPRESS=none: portage cannot read an "
					 "uncompressed gpkg while its own BINPKG_COMPRESS "
					 "is set, so this package will be readable by "
					 "qmerge only");
				warned = true;
			}
			return "";
		}
		for (i = 0; i < ARRAY_SIZE(qgpkg_codecs); i++) {
			if (strcmp(binpkg_compress, qgpkg_codecs[i].name) != 0)
				continue;
			if (qgpkg_codecs[i].add(a) != ARCHIVE_OK)
				err("BINPKG_COMPRESS=%s is not supported by this "
					"libarchive", binpkg_compress);
			qgpkg_compress_flags(a, qgpkg_codecs[i].name);
			return qgpkg_codecs[i].ext;
		}
		err("unsupported BINPKG_COMPRESS: %s", binpkg_compress);
	}

	for (i = 0; i < ARRAY_SIZE(qgpkg_codecs); i++) {
		if (strcmp(qgpkg_codecs[i].name, "lzip") == 0)
			break;
		if (qgpkg_codecs[i].add(a) == ARCHIVE_OK) {
			qgpkg_compress_flags(a, qgpkg_codecs[i].name);
			return qgpkg_codecs[i].ext;
		}
	}

	/* none, no filtering */
	return "";
}

/* detached-sign path into sigpath via the shared signing "engine" 
 * (we call it signing engine now)*/
static int
qgpkg_sign_file(const char *path, const char *sigpath)
{
	struct gpgsign g;
	char           buf[BUFSIZ * 8];
	ssize_t        rd;
	int            fd;
	int            sfd;
	char          *sig    = NULL;
	size_t         siglen = 0;

	fd = open(path, O_RDONLY);
	if (fd < 0)
		return -1;
	if (gpgsign_start(true, &g) != 0) {
		close(fd);
		return -1;
	}
	while ((rd = read(fd, buf, sizeof(buf))) > 0)
		if (gpgsign_feed(&g, buf, (size_t)rd) != 0) {
			rd = -1;
			break;
		}
	close(fd);
	if (rd < 0) {
		gpgsign_abort(&g);
		warn("GnuPG signing failed");
		return -1;
	}
	if (gpgsign_finish(&g, &sig, &siglen) != 0)
		return -1;
	sfd = open(sigpath, O_WRONLY | O_CREAT | O_TRUNC,
			   S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
	if (sfd < 0 || safe_write(sfd, sig, siglen) < 0) {
		if (sfd >= 0)
			close(sfd);
		free(sig);
		return -1;
	}
	close(sfd);
	free(sig);
	return 0;
}

static bool
qgpkg_add_member(struct archive *a, const char *path, const char *entname)
{
	struct archive_entry *entry;
	struct stat           st;
	char                  buf[BUFSIZ * 8];
	ssize_t               len;
	int                   fd;
	bool                  ok = true;

	fd = open(path, O_RDONLY);
	if (fd < 0 || fstat(fd, &st) < 0) {
		if (fd >= 0)
			close(fd);
		return false;
	}
	entry = archive_entry_new();
	archive_entry_set_pathname(entry, entname);
	archive_entry_set_size(entry, st.st_size);
	archive_entry_set_mtime(entry, st.st_mtime, 0);
	archive_entry_set_filetype(entry, AE_IFREG);
	archive_entry_set_perm(entry, 0644);
	archive_write_header(a, entry);
	while ((len = read(fd, buf, sizeof(buf))) > 0)
		if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
			ok = false;
			break;
		}
	if (len < 0)
		ok = false;
	archive_entry_free(entry);
	close(fd);
	return ok;
}
#endif

/* libarchive imlpementation over the old format 
 * needs a little more docs love here */
static bool
qpkg_write_image(struct archive *a, tree_pkg_ctx *pkg, char *line,
				 const char *prefix)
{
	struct archive *ard;
	struct archive_entry *entry;
	struct archive_entry *sparse;
	struct archive_entry_linkresolver *lres;
	struct stat st;
	char ename[BUFSIZE];
	char buf[BUFSIZE * 4];
	char *savep;
	const char *fname;
	int fd;
	ssize_t len;
	size_t plen = strlen(prefix);
	int portroot_fd = tree_pkg_get_portroot_fd(pkg);
	bool gerr = false;

	ard = archive_read_disk_new();
	lres = archive_entry_linkresolver_new();
	archive_entry_linkresolver_set_strategy(lres, archive_format(a));
	for (; (line = strtok_r(line, "\n", &savep)) != NULL; line = NULL) {
		contents_entry *e;
		e = contents_parse_line(line);
		if (!e)
			continue;
		if (check_pkg_install_mask(e->name) != 0)
			continue;
		if (e->name[0] == '/')
			e->name++;
		switch (e->type) {
			case CONTENTS_OBJ:
				if (verbose) {
					char *hash = hash_file_at(portroot_fd, e->name, HASH_MD5);
					if (hash != NULL) {
						if (strcmp(e->digest, hash) != 0)
							warn("MD5 mismatch: expected %s got %s for %s",
									e->digest, hash, e->name);
					}
				}

				if ((fd = openat(portroot_fd, e->name, O_RDONLY)) < 0)
					continue;
				if (fstat(fd, &st) < 0) {
					close(fd);
					continue;
				}

				entry = archive_entry_new();
				snprintf(ename, sizeof(ename), "%s%s", prefix, e->name);
				archive_entry_set_pathname(entry, ename);
				archive_entry_copy_stat(entry, &st);
				(void)archive_read_disk_entry_from_file(ard, entry, fd, &st);
				archive_entry_set_pathname(entry, ename);
				archive_entry_linkify(lres, &entry, &sparse);
				archive_write_header(a, entry);
				if (sparse != NULL) {
					archive_write_header(a, sparse);
					archive_entry_free(entry);
					entry = sparse;
				}
				if (archive_entry_size(entry) > 0)
				{
					while ((len = read(fd, buf, sizeof(buf))) > 0)
						if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
							gerr = true;
							break;
						}
					if (len < 0)
						gerr = true;
				}
				archive_entry_free(entry);
				close(fd);
				break;
			case CONTENTS_SYM:
				/* like for files, we take whatever is in the filesystem */
				if ((len = readlinkat(portroot_fd,
									  e->name, ename, sizeof(ename) - 1)) < 0)
					snprintf(ename, sizeof(ename), "%s", e->sym_target);
				else
					ename[len] = '\0';

				if (verbose) {
					if (strcmp(e->sym_target, ename) != 0)
						warn("symlink target mismatch: "
							 "expected %s got %s for %s",
							 e->sym_target, ename, e->name);
				}

				entry = archive_entry_new();
				archive_entry_set_symlink(entry, ename);
				snprintf(ename, sizeof(ename), "%s%s", prefix, e->name);
				archive_entry_set_pathname(entry, ename);
				if (fstatat(portroot_fd,
							e->name, &st, AT_SYMLINK_NOFOLLOW) < 0)
				{
					archive_entry_set_mtime(entry, e->mtime, 0);
					archive_entry_set_filetype(entry, AE_IFLNK);
					archive_entry_set_mode(entry, 0777);
				} else {
					archive_entry_copy_stat(entry, &st);
				}
				archive_write_header(a, entry);
				archive_entry_free(entry);
				break;
			case CONTENTS_DIR:
				if ((fd = openat(portroot_fd, e->name, O_RDONLY)) < 0)
					continue;
				if (fstat(fd, &st) < 0) {
					close(fd);
					continue;
				}

				entry = archive_entry_new();
				snprintf(ename, sizeof(ename), "%s%s", prefix, e->name);
				archive_entry_set_pathname(entry, ename);
				archive_entry_copy_stat(entry, &st);
				(void)archive_read_disk_entry_from_file(ard, entry, fd, &st);
				archive_entry_set_pathname(entry, ename);
				close(fd);
				archive_write_header(a, entry);
				archive_entry_free(entry);
				break;
		}
	}
	do {
		entry = NULL;
		archive_entry_linkify(lres, &entry, &sparse);
		if (entry == NULL)
			break;

		/* these are hardlinks which apparently have targets outside of
		 * the package's know filelist, e.g. the user adding a hardlink,
		 * we need to process them now depending on the archive format,
		 * which means we'll have to lookup the files to get their body */
		fname = archive_entry_pathname(entry);
		if (fname == NULL ||
			strncmp(fname, prefix, plen) != 0 ||
			fname[plen] == '\0')
			/* not something we would've produced */
			continue;
		fname += plen;

		if ((fd = openat(portroot_fd, fname, O_RDONLY)) < 0)
			continue;

		archive_write_header(a, entry);
		while ((len = read(fd, buf, sizeof(buf))) > 0)
			if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
				gerr = true;
				break;
			}
		if (len < 0)
			gerr = true;
		archive_entry_free(entry);
		close(fd);
	} while (true);
	archive_entry_linkresolver_free(lres);
	archive_read_free(ard);

	return gerr;
}

static int
qgpkg_make(tree_pkg_ctx *pkg, qpkg_cb_args *args)
{
#ifdef ENABLE_GPKG
	struct archive *a;
	struct archive_entry *entry;
	struct stat st;
	struct dirent **files = NULL;
	char tmpdir[BUFSIZE];
	char gpkg[BUFSIZE + 32];
	char buf[BUFSIZE * 4];
	char ename[BUFSIZE];
	const char *filter;
	char *line;
	int i;
	int cnt;
	int dirfd;
	int fd;
	int mfd;
	mode_t mask;
	depend_atom *atom = tree_pkg_atom(pkg, false);
	int portroot_fd = tree_pkg_get_portroot_fd(pkg);
	ssize_t len;
	int tdlen;
	bool gerr = false;
	bool sign = contains_set("binpkg-signing", features) != NULL;

	if (pretend) {
		printf(" %s-%s %s:\n",
				GREEN, NORM, atom_format("%[CATEGORY]%[PF]%[BUILDID]", atom));
		return 0;
	}

	if (sign && !gpgsign_vars_ok())
		return -1;

	if (args != NULL)
		qprintf(">>> Creating binpkg\n");

	line = tree_pkg_meta(pkg, Q_CONTENTS);
	if (line == NULL)
		return -1;

	snprintf(tmpdir, sizeof(tmpdir), "%s%s/qpkg.XXXXXX", portroot, pkgdir);
	mask = umask(S_IRWXG | S_IRWXO);
	i = mkstemp(tmpdir);
	umask(mask);
	if (i == -1)
		return -2;
	close(i);
	unlink(tmpdir);
	if (mkdir(tmpdir, 0750))
		return -3;
	tdlen = (int)MIN(strlen(tmpdir), (size_t)4064);

	printf(" %s-%s %s: ", GREEN, NORM,
		   atom_format("%[CATEGORY]%[PF]%[BUILDID]", atom));
	fflush(stdout);

	snprintf(buf, sizeof(buf), "%.*s/Manifest", tdlen, tmpdir);
	mfd = open(buf, O_WRONLY | O_CREAT | O_TRUNC,
			   S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
	if (mfd < 0) {
		rmdir(tmpdir);
		printf("%sFAIL%s\n", RED, NORM);
		return -4;
	}

	snprintf(buf, sizeof(buf), "%.*s/gpkg-1", tdlen, tmpdir);
	fd = open(buf, O_WRONLY | O_CREAT | O_TRUNC,
			  S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
	if (fd < 0) {
		close(mfd);
		rm_rf(tmpdir);
		printf("%sFAIL%s\n", RED, NORM);
		return -5;
	}
	/* contractually we don't have to put anything in here, but we drop
	 * our signature so it can be traced back to us */
	len = snprintf(ename, sizeof(ename), "portage-utils-%s", VERSION);
	if (safe_write(fd, ename, (size_t)len) < 0)
		warnp("could not write self-identifier");
	close(fd);
	write_hashes(buf, "DATA", mfd);

	/* we first 1. create metadata (vdb), 2. image (actual data) and
	 * then 3. the container gpkg image */

	/* 1. VDB into metadata.tar.zst */
	a = archive_write_new();
	archive_write_set_format_ustar(a);  /* as required by GLEP-78 */
	filter = qgpkg_set_compression(a);
	snprintf(gpkg, sizeof(gpkg), "%.*s/metadata.tar%s", tdlen, tmpdir, filter);
	if (archive_write_open_filename(a, gpkg) != ARCHIVE_OK)
		gerr = true;

	cnt = 0;
	if ((dirfd = openat(portroot_fd,
						tree_pkg_get_path(pkg),
						O_RDONLY)) >= 0)
		cnt = scandirat(dirfd, ".", &files, filter_self_parent, alphasort);
	for (i = 0; i < cnt; i++) {
		if (atom->BUILDID > 0 &&
				strcmp(files[i]->d_name, "BUILD_ID") == 0)
			continue;
		if ((fd = openat(dirfd, files[i]->d_name, O_RDONLY)) < 0)
			continue;
		if (fstat(fd, &st) < 0 || !S_ISREG(st.st_mode)) {
			close(fd);
			continue;
		}

		entry = archive_entry_new();
		snprintf(ename, sizeof(ename), "metadata/%s", files[i]->d_name);
		archive_entry_set_pathname(entry, ename);
		archive_entry_set_size(entry, st.st_size);
		archive_entry_set_mtime(entry, st.st_mtime, 0);
		archive_entry_set_filetype(entry, AE_IFREG);
		archive_entry_set_perm(entry, 0644);
		archive_write_header(a, entry);
		while ((len = read(fd, buf, sizeof(buf))) > 0)
			if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
				gerr = true;
				break;
			}
		if (len < 0)
			gerr = true;
		close(fd);
		archive_entry_free(entry);
	}
	if (atom->BUILDID > 0) {
		entry = archive_entry_new();
		archive_entry_set_pathname(entry, "metadata/BUILD_ID");
		len = snprintf(ename, sizeof(ename), "%u\n", atom->BUILDID);
		archive_entry_set_size(entry, (size_t)len);
		archive_entry_set_mtime(entry, time(NULL), 0);
		archive_entry_set_filetype(entry, AE_IFREG);
		archive_entry_set_perm(entry, 0644);
		if (archive_write_header(a, entry) != ARCHIVE_OK ||
				archive_write_data(a, ename, (size_t)len) != (la_ssize_t)len)
			gerr = true;
		archive_entry_free(entry);
	}
	if (archive_write_close(a) != ARCHIVE_OK)
		gerr = true;
	archive_write_free(a);
	scandir_free(files, cnt);
	if (dirfd >= 0)
		close(dirfd);
	write_hashes(gpkg, "DATA", mfd);

	/* 2. the actual files into image.tar.zst taking GLEP-78 mandates ustar into account */
	a = archive_write_new();
	archive_write_set_format_pax_restricted(a);
	filter = qgpkg_set_compression(a);
	snprintf(gpkg, sizeof(gpkg), "%.*s/image.tar%s", tdlen, tmpdir, filter);
	if (archive_write_open_filename(a, gpkg) != ARCHIVE_OK)
		gerr = true;
	if (qpkg_write_image(a, pkg, line, "image/"))
		gerr = true;
	if (archive_write_close(a) != ARCHIVE_OK)
		gerr = true;
	archive_write_free(a);
	write_hashes(gpkg, "DATA", mfd);

	/* 3. the final gpkg file (to be renamed properly when it all
	 * succeeds */
	snprintf(gpkg, sizeof(gpkg), "%.*s/bin.gpkg.tar", tdlen, tmpdir);
	a = archive_write_new();
	archive_write_set_format_ustar(a);  /* as required by GLEP-78 */
	if (archive_write_open_filename(a, gpkg) != ARCHIVE_OK)
		gerr = true;

	if (atom->BUILDID > 0)
		i = snprintf(ename, sizeof(ename), "%s-%u", atom->PF, atom->BUILDID);
	else
		i = snprintf(ename, sizeof(ename), "%s", atom->PF);

	/* 3.1 the package format identifier file gpkg-1 */
	snprintf(buf, sizeof(buf), "%.*s/gpkg-1", tdlen, tmpdir);
	if ((fd = open(buf, O_RDONLY)) >= 0 &&
		fstat(fd, &st) >= 0)
	{
		entry = archive_entry_new();
		snprintf(ename + i, sizeof(ename) - i, "/gpkg-1");
		archive_entry_set_pathname(entry, ename);
		archive_entry_set_size(entry, st.st_size);
		archive_entry_set_mtime(entry, st.st_mtime, 0);
		archive_entry_set_filetype(entry, AE_IFREG);
		archive_entry_set_perm(entry, 0644);
		archive_write_header(a, entry);
		while ((len = read(fd, buf, sizeof(buf))) > 0)
			if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
				gerr = true;
				break;
			}
		if (len < 0)
			gerr = true;
		archive_entry_free(entry);
	} else
		gerr = true;
	if (fd >= 0)
		close(fd);

	/* 3.2 the metadata archive metadata.tar${comp} */
	snprintf(buf, sizeof(buf), "%.*s/metadata.tar%s", tdlen, tmpdir, filter);
	/* this must succeed, no? */
	if ((fd = open(buf, O_RDONLY)) >= 0 &&
		fstat(fd, &st) >= 0)
	{
		entry = archive_entry_new();
		snprintf(ename + i, sizeof(ename) - i, "/metadata.tar%s", filter);
		archive_entry_set_pathname(entry, ename);
		archive_entry_set_size(entry, st.st_size);
		archive_entry_set_mtime(entry, st.st_mtime, 0);
		archive_entry_set_filetype(entry, AE_IFREG);
		archive_entry_set_perm(entry, 0644);
		archive_write_header(a, entry);
		while ((len = read(fd, buf, sizeof(buf))) > 0)
			if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
				gerr = true;
				break;
			}
		if (len < 0)
			gerr = true;
		archive_entry_free(entry);
	} else
		gerr = true;
	if (fd >= 0)
		close(fd);

	/* 3.3 the metadata signature (FEATURES=binpkg-signing) */
	if (sign && !gerr) {
		char sigf[BUFSIZE * 4 + 5];

		snprintf(buf, sizeof(buf), "%.*s/metadata.tar%.16s",
				 tdlen, tmpdir, filter);
		snprintf(sigf, sizeof(sigf), "%.4090s.sig", buf);
		snprintf(ename + i, sizeof(ename) - i, "/metadata.tar%.16s.sig",
				 filter);
		if (qgpkg_sign_file(buf, sigf) != 0 ||
				!qgpkg_add_member(a, sigf, ename))
			gerr = true;
		else
			write_hashes(sigf, "DATA", mfd);
	}

	/* 3.4 the filesystem image archive image.tar${comp} */
	snprintf(buf, sizeof(buf), "%.*s/image.tar%s", tdlen, tmpdir, filter);
	/* this must succeed, no? */
	if ((fd = open(buf, O_RDONLY)) >= 0 &&
		fstat(fd, &st) >= 0)
	{
		entry = archive_entry_new();
		snprintf(ename + i, sizeof(ename) - i, "/image.tar%s", filter);
		archive_entry_set_pathname(entry, ename);
		archive_entry_set_size(entry, st.st_size);
		archive_entry_set_mtime(entry, st.st_mtime, 0);
		archive_entry_set_filetype(entry, AE_IFREG);
		archive_entry_set_perm(entry, 0644);
		archive_write_header(a, entry);
		while ((len = read(fd, buf, sizeof(buf))) > 0)
			if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
				gerr = true;
				break;
			}
		if (len < 0)
			gerr = true;
		archive_entry_free(entry);
	} else
		gerr = true;
	if (fd >= 0)
		close(fd);

	/* 3.5 the image signature (FEATURES=binpkg-signing) */
	if (sign && !gerr) {
		char sigf[BUFSIZE * 4 + 5];

		snprintf(buf, sizeof(buf), "%.*s/image.tar%.16s",
				 tdlen, tmpdir, filter);
		snprintf(sigf, sizeof(sigf), "%.4090s.sig", buf);
		snprintf(ename + i, sizeof(ename) - i, "/image.tar%.16s.sig",
				 filter);
		if (qgpkg_sign_file(buf, sigf) != 0 ||
				!qgpkg_add_member(a, sigf, ename))
			gerr = true;
		else
			write_hashes(sigf, "DATA", mfd);
	}

	/* 3.6 the package Manifest data file Manifest (clear-signed under
	 * FEATURES=binpkg-signing) */
	close(mfd);
	if (sign && !gerr) {
		struct stat mst;
		char       *mtxt   = NULL;
		char       *msig   = NULL;
		size_t      msiglen = 0;
		int         cfd;

		snprintf(buf, sizeof(buf), "%.*s/Manifest", tdlen, tmpdir);
		cfd = open(buf, O_RDONLY);
		if (cfd < 0 || fstat(cfd, &mst) < 0) {
			if (cfd >= 0)
				close(cfd);
			gerr = true;
		} else {
			mtxt = xmalloc((size_t)mst.st_size + 1);
			if (safe_read(cfd, mtxt, (size_t)mst.st_size) < 0)
				gerr = true;
			close(cfd);
			if (!gerr &&
					gpgsign_buf(mtxt, (size_t)mst.st_size, false,
								&msig, &msiglen) != 0)
				gerr = true;
			if (!gerr) {
				cfd = open(buf, O_WRONLY | O_TRUNC);
				if (cfd < 0 || safe_write(cfd, msig, msiglen) < 0)
					gerr = true;
				if (cfd >= 0)
					close(cfd);
			}
			free(mtxt);
			free(msig);
		}
	}
	snprintf(buf, sizeof(buf), "%.*s/Manifest", tdlen, tmpdir);
	if ((fd = open(buf, O_RDONLY)) >= 0 &&
		fstat(fd, &st) >= 0)
	{
		entry = archive_entry_new();
		snprintf(ename + i, sizeof(ename) - i, "/Manifest");
		archive_entry_set_pathname(entry, ename);
		archive_entry_set_size(entry, st.st_size);
		archive_entry_set_mtime(entry, st.st_mtime, 0);
		archive_entry_set_filetype(entry, AE_IFREG);
		archive_entry_set_perm(entry, 0644);
		archive_write_header(a, entry);
		while ((len = read(fd, buf, sizeof(buf))) > 0)
			if (archive_write_data(a, buf, (size_t)len) != (la_ssize_t)len) {
				gerr = true;
				break;
			}
		if (len < 0)
			gerr = true;
		archive_entry_free(entry);
	} else
		gerr = true;
	if (fd >= 0)
		close(fd);

	if (archive_write_close(a) != ARCHIVE_OK)
		gerr = true;
	archive_write_free(a);

	/* create dirs, if necessary */
	if (atom->BUILDID > 0)
		i = snprintf(buf, sizeof(buf), "%s%s/%s/%s",
					 portroot, pkgdir, atom->CATEGORY, atom->PN);
	else
		i = snprintf(buf, sizeof(buf), "%s%s/%s",
					 portroot, pkgdir, atom->CATEGORY);
	mkdir_p(buf, 0755);

	if (atom->BUILDID > 0)
		snprintf(buf + i, sizeof(buf) - i, "/%s-%u.gpkg.tar",
				 atom->PF, atom->BUILDID);
	else
		snprintf(buf + i, sizeof(buf) - i, "/%s.gpkg.tar", atom->PF);

	if (gerr) {
		rm_rf(tmpdir);
		printf("%sFAIL%s\n", RED, NORM);
		return -6;
	}

	if (rename(gpkg, buf)) {
		warnp("could not move '%s' to '%s'", gpkg, buf);
		return 1;
	}

	rm_rf(tmpdir);

	if (stat(buf, &st) == -1) {
		warnp("could not stat '%s'", buf);
		return 1;
	}

	printf("%s%s%s KiB\n",
			RED, make_human_readable_str(st.st_size, 1, KILOBYTE), NORM);

	return 0;
#else
	warnp("gpkg support not compiled in");
	(void)pkg;
	(void)args;
	return 1;
#endif
}

/* now xattrs/acls/sparse/hardlinks are identified and defined, so those flags are satisfied.
 * anything else is warned about and ignored */
static void
qpkg_tar_opts_check(void)
{
	static bool done = false;
	char *tmp;
	char *tok;
	char *savep;

	if (done)
		return;
	done = true;
	if (binpkg_tar_opts == NULL || binpkg_tar_opts[0] == '\0')
		return;
	tmp = xstrdup(binpkg_tar_opts);
	for (tok = strtok_r(tmp, " \t", &savep);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t", &savep))
	{
		if (strcmp(tok, "--xattrs") == 0 ||
			strcmp(tok, "--acls") == 0 ||
			strcmp(tok, "--sparse") == 0 ||
			strncmp(tok, "--xattrs-include=",
					sizeof("--xattrs-include=") - 1) == 0)
			continue;
		warn("PORTAGE_BINPKG_TAR_OPTS: '%s' not supported by the "
			 "built-in packer, ignored", tok);
	}
	free(tmp);
}

static int
qpkg_make(tree_pkg_ctx *pkg, qpkg_cb_args *args)
{
	FILE *fp;
	struct archive *a;
	char tmpdir[BUFSIZE];
	char tbz2[BUFSIZE + 32];
	char buf[BUFSIZE * 4];
	char footer[4] = { 0 };
	size_t xpaksize;
	char *line;
	int i;
	char *xpak_argv[2];
	struct stat st;
	mode_t mask;
	int tdlen;
	bool gerr = false;
	depend_atom *atom = tree_pkg_atom(pkg, false);

	if (pretend) {
		printf(" %s-%s %s:\n",
				GREEN, NORM, atom_format("%[CATEGORY]%[PF]%[BUILDID]", atom));
		return 0;
	}


	if (args != NULL)
		qprintf(">>> Creating binpkg\n");

	line = tree_pkg_meta(pkg, Q_CONTENTS);
	if (line == NULL)
		return -1;

	snprintf(tmpdir, sizeof(tmpdir), "%s%s/qpkg.XXXXXX", portroot, pkgdir);
	mask = umask(0077);
	i = mkstemp(tmpdir);
	umask(mask);
	if (i == -1)
		return -2;
	close(i);
	unlink(tmpdir);
	if (mkdir(tmpdir, 0750))
		return -3;
	/* ISO C only guarantees 4095 bytes of snprintf output.  */
	tdlen = (int)MIN(strlen(tmpdir), (size_t)4064);

	printf(" %s-%s %s: ", GREEN, NORM,
			atom_format("%[CATEGORY]%[PF]%[BUILDID]", atom));
	fflush(stdout);

	qpkg_tar_opts_check();

	snprintf(tbz2, sizeof(tbz2), "%.*s/bin.tbz2", tdlen, tmpdir);
	a = archive_write_new();
	archive_write_set_format_pax_restricted(a);
	if (archive_write_add_filter_bzip2(a) != ARCHIVE_OK)
		gerr = true;
	if (archive_write_open_filename(a, tbz2) != ARCHIVE_OK)
		gerr = true;
	if (qpkg_write_image(a, pkg, line, ""))
		gerr = true;
	if (archive_write_close(a) != ARCHIVE_OK)
		gerr = true;
	archive_write_free(a);
	if (gerr) {
		warn("failed to create image for '%s'", tbz2);
		return 2;
	}

	if ((i = open(tbz2, O_WRONLY)) < 0) {
		warnp("failed to open '%s'", tbz2);
		return 1;
	}

	/* get offset where xpak will start */
	if (fstat(i, &st) == -1) {
		warnp("could not stat '%s'", tbz2);
		close(i);
		return 1;
	}
	xpaksize = st.st_size;

	xpak_argv[0] = tree_pkg_get_path(pkg);
	/* in case of multi-instance build we pack the VDB files individually so the
	 * recorded BUILD_ID can be replaced by this instance's id */
	xpak_argv[1] = NULL;
	if (atom->BUILDID > 0) {

		struct dirent **mfiles = NULL;
		char          **margv;
		char            bidf[BUFSIZE + 32];
		FILE           *bf;
		int             mcnt   = 0;
		int             margc  = 0;
		int             mdirfd;
		int             mi;
		int             xr     = 1;

		mdirfd = open(xpak_argv[0], O_RDONLY);
		if (mdirfd >= 0)
			mcnt = scandirat(mdirfd, ".", &mfiles,
							 filter_self_parent, alphasort);
		snprintf(bidf, sizeof(bidf), "%.*s/BUILD_ID", tdlen, tmpdir);
		bf = fopen(bidf, "w");
		if (bf != NULL) {
			bool bok = fprintf(bf, "%u\n", atom->BUILDID) > 0;

			if (fclose(bf) != 0)
				bok = false;
			if (bok && mcnt > 0) {
				margv = xmalloc(sizeof(char *) * (mcnt + 1));
				for (mi = 0; mi < mcnt; mi++) {
					if (strcmp(mfiles[mi]->d_name, "BUILD_ID") == 0)
						continue;
					xasprintf(&margv[margc], "%s/%s",
							  xpak_argv[0], mfiles[mi]->d_name);
					margc++;
				}
				margv[margc++] = xstrdup(bidf);
				xr = xpak_create(AT_FDCWD, tbz2, margc, margv, 1, verbose);
				for (mi = 0; mi < margc; mi++)
					free(margv[mi]);
				free(margv);
			}
		}
		scandir_free(mfiles, mcnt);
		if (mdirfd >= 0)
			close(mdirfd);
		unlink(bidf);
		if (xr != 0) {
			warn("failed to create xpak archive for '%s'", tbz2);
			close(i);
			return 1;
		}
	} else if (xpak_create(AT_FDCWD, tbz2, 1, xpak_argv, 1, verbose) != 0) {
		warn("failed to create xpak archive for '%s'", tbz2);
		close(i);
		return 1;
	}

	/* calculate the number of bytes taken by the xpak archive */
	if (fstat(i, &st) == -1) {
		warnp("could not stat '%s'", tbz2);
		close(i);
		return 1;
	}
	xpaksize = st.st_size - xpaksize;

	/* save tbz2 tail: OOOOSTOP */
	if ((fp = fdopen(i, "a")) == NULL) {
		warnp("could not open '%s'", tbz2);
		close(i);
		return 1;
	}

	WRITE_BE_INT32(footer, xpaksize);
	{
		bool footer_ok = fwrite(footer, 1, 4, fp) == 4 &&
						 fwrite("STOP", 1, 4, fp) == 4;
		if (fclose(fp) != 0)
			footer_ok = false;
		if (!footer_ok) {
			warn("failed to write xpak footer to '%s'", tbz2);
			return 1;
		}
	}

	/* create dirs, if necessary */
	if (atom->BUILDID > 0)
		i = snprintf(buf, sizeof(buf), "%s%s/%s/%s",
					 portroot, pkgdir, atom->CATEGORY, atom->PN);
	else
		i = snprintf(buf, sizeof(buf), "%s%s/%s",
					 portroot, pkgdir, atom->CATEGORY);
	mkdir_p(buf, 0755);

	if (atom->BUILDID > 0)
		snprintf(buf + i, sizeof(buf) - i, "/%s-%u.xpak",
				 atom->PF, atom->BUILDID);
	else
		snprintf(buf + i, sizeof(buf) - i, "/%s.tbz2", atom->PF);
	if (rename(tbz2, buf)) {
		warnp("could not move '%s' to '%s'", tbz2, buf);
		return 1;
	}

	rmdir(tmpdir);

	if (stat(buf, &st) == -1) {
		warnp("could not stat '%s'", buf);
		return 1;
	}

	printf("%s%s%s KiB\n",
			RED, make_human_readable_str(st.st_size, 1, KILOBYTE), NORM);

	return 0;
}

int
qpkg_backup(tree_pkg_ctx *pkg)
{
	int ret;
	int cwd = open(".", O_RDONLY | O_CLOEXEC);

	if (cwd < 0)
		return 1;
	if (chdir(portroot) != 0) {
		close(cwd);
		return 1;
	}
	if (strcmp(binpkg_format, "gpkg") == 0)
		ret = qgpkg_make(pkg, NULL);
	else
		ret = qpkg_make(pkg, NULL);
	if (fchdir(cwd) != 0)
		ret = 1;
	close(cwd);
	return ret;
}

static int
qpkg_cb(tree_pkg_ctx *pkg, void *priv)
{
	qpkg_cb_args *args = priv;

	/* check atoms to compute a build-id */
	if (contains_set("binpkg-multi-instance", features)) {
		atom_ctx *atom = tree_pkg_atom(pkg, false);
		array    *m    = tree_match_atom(args->binpkg, atom, TREE_MATCH_FIRST);
		if (array_cnt(m) > 0) {
			tree_pkg_ctx *p = array_get(m, 0);
			atom->BUILDID = tree_pkg_atom(p, false)->BUILDID;
		}
		array_free(m);

		/* take the next, we should always start at 1, so either way
		 * this is fine */
		atom->BUILDID++;
	}

	if (args->build_gpkg) {
		if (qgpkg_make(pkg, args) == 0)
			args->pkgs_made++;
	} else {
		if (qpkg_make(pkg, args) == 0)
			args->pkgs_made++;
	}

	return 0;
}

int qpkg_main(int argc, char **argv)
{
	size_t s;
	int i;
	struct stat st;
	depend_atom *atom;
	int restrict_chmod = 0;
	int qclean = 0;
	int fd;
	char bindir[_Q_PATH_MAX];
	qpkg_cb_args cb_args;

	memset(&cb_args, 0, sizeof(cb_args));

	cb_args.bindir     = pkgdir;
	cb_args.build_gpkg = strcmp(binpkg_format, "gpkg") == 0;

	while ((i = GETOPT_LONG(QPKG, qpkg, "")) != -1) {
		switch (i) {
		case 'E': cb_args.clean_notintree = true;  /* fall through */
		case 'c': qclean = 1;                       break;
		case 'g': cb_args.build_gpkg = true;        break;
		case 'x': cb_args.build_gpkg = false;       break;
		case 'p': pretend = 1;                      break;
		case 'P':
			restrict_chmod = 1;
			cb_args.bindir = optarg;
			if (access(cb_args.bindir, W_OK) != 0)
				errp("%s", cb_args.bindir);
			break;
		COMMON_GETOPTS_CASES(qpkg)
		}
	}

	/* setup temp dirs */
	if (cb_args.bindir[0] != '/')
		err("'%s' is not a valid package destination", cb_args.bindir);
	/* brute force just unlink any file or symlink, if this fails, it's
	 * actually good :) */
	snprintf(bindir, sizeof(bindir), "%s%s", portroot, cb_args.bindir);
	unlink(bindir);
	fd = open(bindir, O_RDONLY);
	if (fd == -1) {
		if (mkdir(bindir, 0750) == -1)
			errp("could not create packages directory '%s'", bindir);
		fd = open(bindir, O_RDONLY | O_DIRECTORY | O_NOFOLLOW);
		if (fd == -1)
			errp("could not open packages directory '%s'", bindir);
		if (!restrict_chmod && fchmod(fd, 0750) != 0)
			errp("could not chmod(0750) packages directory '%s'", bindir);
		close(fd);
	} else {
		if (fstat(fd, &st) == -1 || !S_ISDIR(st.st_mode))
			errp("could not create packages directory '%s'", bindir);
		close(fd);
	}
	if (access(bindir, W_OK) != 0)
		err("No write access to '%s'", bindir);
	cb_args.binpkg = tree_new(portroot, cb_args.bindir, TREETYPE_BINPKG, false);
	if (cb_args.binpkg == NULL)
		return EXIT_FAILURE;

	cb_args.vdb = tree_new(portroot, portvdb, TREETYPE_VDB, false);
	if (!cb_args.vdb)
	{
		tree_close(cb_args.binpkg);
		return EXIT_FAILURE;
	}

	if (qclean) {
		int ret = qpkg_clean(&cb_args);
		tree_close(cb_args.vdb);
		tree_close(cb_args.binpkg);
		return ret;
	}

	if (argc == optind) {
		tree_close(cb_args.vdb);
		tree_close(cb_args.binpkg);
		qpkg_usage(EXIT_FAILURE);
	}

	/* we have to change to the root so that we can feed the full paths
	 * to tar when we create the binary package. */
	xchdir(portroot);

	/* first process any arguments which point to /var/db/pkg, an
	 * undocumented method to allow easily tab-completing into vdb as
	 * arguments, the trailing / needs to be present for this (as tab
	 * completion would do) */
	s = strlen(portvdb);
	for (i = optind; i < argc; i++) {
		size_t asize = strlen(argv[i]);
		if (asize == 0) {
			argv[i] = NULL;
			continue;
		}
		if (asize > s && argv[i][0] == '/' && argv[i][asize - 1] == '/') {
			char *path = argv[i];

			/* chop off trailing / */
			argv[i][asize - 1] = '\0';

			/* eliminate duplicate leading /, we know it starts with / */
			while (path[1] == '/')
				path++;

			if (strncmp(portvdb, path, s) == 0) {
				path += s + 1 /* also eat / after portvdb */;
				argv[i] = path;
			} else {
				argv[i][asize - 1] = '/';  /* restore, it may be a cat match */
			}
		}
	}

	/* now try to run through vdb and locate matches for user inputs */
	for (i = optind; i < argc; i++) {
		if (argv[i] == NULL)
			continue;
		if (strcmp(argv[i], "world") == 0) {
			/* this is a crude workaround, we include all packages for this,
			 * which isn't exactly @world, but all its deps too */
			tree_foreach_pkg_fast(cb_args.vdb, qpkg_cb, &cb_args, NULL);
			break;  /* no point in continuing since we did everything */
		}
		atom = atom_explode(argv[i]);
		if (atom == NULL)
			continue;

		s = cb_args.pkgs_made;
		tree_foreach_pkg_fast(cb_args.vdb, qpkg_cb, &cb_args, atom);
		if (s == cb_args.pkgs_made)
			warn("no match for '%s'", argv[i]);
		atom_implode(atom);
	}
	tree_close(cb_args.vdb);
	tree_close(cb_args.binpkg);

	if (cb_args.pkgs_made > 0)
		qprintf(" %s*%s Packages can be found in %s\n",
				GREEN, NORM, cb_args.bindir);

	return (cb_args.pkgs_made > 0 ? EXIT_SUCCESS : EXIT_FAILURE);
}
