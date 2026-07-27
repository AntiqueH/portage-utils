/*
 * Copyright 2005-2026 Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2005-2010 Ned Ludd        - <solar@gentoo.org>
 * Copyright 2005-2014 Mike Frysinger  - <vapier@gentoo.org>
 * Copyright 2018-2026 Fabian Groffen  - <grobian@gentoo.org>
 * Copyright 2026-     Jaeger H.  	   - <antiq.hofer@gmail.com>
 */

#include "main.h"
#include "applets.h"

#include <stdio.h>
#include <xalloc.h>
#include <fnmatch.h>
#include <dirent.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <pwd.h>
#include <grp.h>
#include <assert.h>
#include <time.h>
#include <ctype.h>
#include <regex.h>
#include <stdarg.h>

#include <archive.h>
#include <archive_entry.h>
#include <curl/curl.h>
#include <zlib.h>
#if defined(ENABLE_GPKG) && defined(HAVE_GPGME)
# include <gpgme.h>
#endif

#include "stat-time.h"

#include "atom.h"
#include "copy_file.h"
#include "dep.h"
#include "move_file.h"
#include "contents.h"
#include "eat_file.h"
#include "file_magic.h"
#include "hash.h"
#include "human_readable.h"
#include "profile.h"
#include "rmspace.h"
#include "scandirat.h"
#include "set.h"
#include "tree.h"
#include "xasprintf.h"
#include "xchdir.h"
#include "xmkdir.h"
#include "xpak.h"
#include "xsystem.h"

#ifndef GLOB_BRACE
# define GLOB_BRACE     (1 << 10)	/* Expand "{a,b}" to "a" "b".  */
#endif

/*
  --nofiles                        don't verify files in package
  --noscript                       don't execute pkg_{pre,post}{inst,rm} (if any)
*/

/* How things should work, ideally.  This is not how it currently is
 * implemented at all.
 *
 * invocation: qmerge ... pkg/a pkg/b pkg/c
 * initial mergeset: pkg/a pkg/b pkg/c
 * resolving:
 * - for pkg, get dependencies
 *   * apply masks
 *   * extract depend, rdepend, bdepend, etc.
 *   * filter flags in use (libq/dep)
 *   * add found pkgs to mergeset if not present in resolvedset
 * - while mergeset contains pkgs
 *   * resolve pkg (see above)
 *   * move from mergeset to resolvedset
 * here (if all is well) mergeset is empty, and resolvedset contains the
 * pkgs to be installed.  If for instance pkg/c depends on pkg/b it
 * won't occur double, for it is a set.
 *
 * Technically, because we deal with binpkgs, we don't have
 * dependencies, but there can be pre/post scripts that actually use
 * depended on pkgs, and if we would invoke ebuild(5) to compile instead
 * of unpack, we would respect the order too, so the resolvedset here
 * needs to be ordered into a list.
 * While functionally one can re-evaluate the dependencies here,
 * implementation wise, it probably is easier to build the final merge
 * order list while resolving.  This can also add the additional
 * metadata of whether a pkg was requested (cmdline) or pulled in a dep,
 * and for which package.  That information can be leveraged to draw a
 * tree (visuals) but also to determine possible parallel installation
 * paths.
 *
 * For example, original invocation could lead to a resolved merge list
 * of:
 *   M pkg/a
 *   m  pkg/d
 *   R pkg/c
 *   M  pkg/b
 *
 * After this, the pkgs need to be fetched and the pre phases need to be
 * run.  In interactive mode, a question probably needs to be inserted
 * after the printing of the resolved merge list.  Then if all checks
 * out, the unpack and merge to live fs + vdb updates can be performed.
 * Ideally the unpack (or compile via ebuild(5)) phase is separated from
 * the final merge to live fs.  The latter always has to be serial, but
 * the former can run in parallel based on dependencies seen.  For
 * our example, pkg/d and pkg/b can be unpacked in parallel, merged in
 * which order finished first, then pkg/a and pkg/c can commence.  So
 * the start set is pkg/d and pkg/b, and each unlocks pkg/a and pkg/c
 * respectively, which are not constrained, other than the final merge
 * logic.
 *
 * Errors
 * There are multiple kinds of errors in multiple stages.  Whether they
 * are fatal depends on a number of factors.
 * - resolution error
 *   Failing to resolve an atom basically makes the tree that that pkg
 *   is part of unmergable; that is, it needs to be discarded from the
 *   workset.  In interactive mode after resolving we could ask if the
 *   user wants to continue (if there's anything else we *can* do),
 *   non-interactive we could decide to just go ahead with whatever we
 *   was possible, unless we add a flag that stops at resolution errors.
 * - USE-dep resolution error
 *   The state of USE-flags must be respected, and can cause problems,
 *   in particular cyclic dependencies.  Solution to those is to disable
 *   USE-flags temporary and re-merge without.  For now, these errors
 *   are not resolved, but should be detected and treated as resolution
 *   errors above.
 * - fetch error
 *   Either because fetching the binpkg or the source files fails.  This
 *   discards the atom and its tree.  It may be possible in this case to
 *   try and re-resolve using an older version of the pkg.  But since
 *   this kind of error is pretty much in the foundation of the work, it
 *   seems more logical to exclude the tree the package belongs too,
 *   because at this point parallel execution happens, it makes no sense
 *   any more to ask the user to abort.
 * - unpack or merge error
 *   Under these errors are the failures in the various pkg checks (run
 *   phases) and for source-based installs obviously compilation
 *   failures.  These discard an entire tree, and like fetch errors,
 *   we don't have a clear opportunity anymore to ask whether or not to
 *   continue.
 * - live fs + vdb error
 *   This should be rare, but most probably filesystem related errors,
 *   such as running out of diskspace or lacking certain permissions.
 *   Corrupting the VDB hopefully doesn't happen, but it is possible to
 *   encounter problems there as well.  Like fetch and unpack errors, we
 *   should try to continue with whatever we can, but will not roll-back
 *   already merged packages.  So a failure here, should result in
 *   dropping all children from the failed pkg.
 *
 * After merging qlop -Ev should show whatever was merged successfully,
 * so qmerge should show what failed to merge (in what stage).
 */

/* #define BUSYBOX "/bin/busybox" */
#define BUSYBOX ""

#define QMERGE_FLAGS "fFsKUepuDNyOij:" COMMON_FLAGS
static struct option const qmerge_long_opts[] = {
	{"fetch",   no_argument, NULL, 'f'},
	{"force",   no_argument, NULL, 'F'},
	{"search",  no_argument, NULL, 's'},
	{"install", no_argument, NULL, 'K'},
	{"unmerge", no_argument, NULL, 'U'},
	{"erase",   no_argument, NULL, 'e'},
	{"pretend", no_argument, NULL, 'p'},
	{"keepwork",no_argument, NULL, 127},
	{"update",  no_argument, NULL, 'u'},
	{"deep",    no_argument, NULL, 'D'},
	{"newuse",  no_argument, NULL, 'N'},
	{"rebuilt-binaries", no_argument, NULL, 133},
	{"rebuilt-binaries-timestamp", a_argument, NULL, 137},
	{"yes",     no_argument, NULL, 'y'},
	{"nodeps",  no_argument, NULL, 'O'},
	{"index",   no_argument, NULL, 'i'},
	{"fetchonly",no_argument, NULL, 130},
	{"show-phases",no_argument, NULL, 131},
	{"backtrack", a_argument,  NULL, 132},
	{"jobs",    a_argument,  NULL, 'j'},
	{"usepkg-exclude", a_argument, NULL, 134},
	{"usepkg-exclude-live", no_argument, NULL, 135},
	{"binpkg-respect-use", a_argument, NULL, 136},
	{"debug",   no_argument, NULL, 128},
	COMMON_LONG_OPTS
};
static const char * const qmerge_opts_help[] = {
	"Fetch newest Packages index; with package names also fetch those",
	"Fetch package (skipping Packages)",
	"Search the binhost catalog by name (regex; -v lists non-installable)",
	"Install package",
	"Uninstall package",
	"Force-erase: unmerge WITHOUT the shared-file scan (only CONFIG_PROTECT kept)",
	"Pretend only",
	"Do not cleanup the unpacked binpkgs in qmerge tempdir",
	"Update only",
	"Consider the whole dep tree for updates (deep); with -u = emerge -uD",
	"Reinstall binpkgs whose built USE (incl. *_TARGETS) differs from installed",
	"Reinstall same-version binpkgs rebuilt remotely (newer BUILD_TIME)",
	"With --rebuilt-binaries: only rebuilds with BUILD_TIME >= this epoch",
	"Don't prompt before overwriting",
	"Don't merge dependencies",
	"Update the Packages index from PKGDIR (incremental; -F: full rebuild)",
	"Fetch packages (and their deps) into PKGDIR without merging",
	"Print the pkg_* phase functions a binpkg would run at merge time",
	"Conflict-repair rounds during resolution (default 20, 0 disables)",
	"Parallel download jobs: N, 0=one per CPU, y=max, n=serial (default 4)",
	"Never satisfy these atoms from binpkgs (no source fallback: refuses)",
	"Reject binpkgs built from live ebuilds (PROPERTIES=live)",
	"USE gate for candidates: y=all repos incl local, n=off (default: foreign)",
	"Run shell funcs with `set -x`",
	COMMON_OPTS_HELP
};
#define qmerge_usage(ret) usage(ret, QMERGE_FLAGS, qmerge_long_opts, qmerge_opts_help, NULL, lookup_applet_idx("qmerge"))

char search_pkgs = 0;
static char show_phases = 0;
/* backtrack budget: rounds of conflict-repair resolution (portage
 * --backtrack parity: mechanism always active, option caps retries;
 * 0 = single-shot resolve, refuse on conflict) */
static int qm_backtrack = -1;
char interactive = 1;
char install = 0;
char uninstall = 0;
char uninstall_force = 0;
char force_download = 0;
char follow_rdepends = 1;
char qmerge_strict = 0;
char update_only = 0;
static char newuse = 0;
static char rebuilt_bins = 0;
/* --rebuilt-binaries-timestamp: BUILD_TIME floor for rebuild pulls */
static unsigned long long qm_rebuilt_ts = 0;
char deep = 0;   /* -D: recurse the whole tree, upgrading satisfied deps too */
char fetch_only = 0;
int  qmerge_jobs = -1;  /* parallel download workers; -1 until resolved from
						 * -j, then $QMERGE_JOBS, else the default (4) */
bool keep_work = false;
bool debug = false;
const char Packages[] = "Packages";

struct llist_char_t {
	char *data;
	struct llist_char_t *next;
};

typedef struct llist_char_t llist_char;

static void pkg_fetch(int, const depend_atom *, tree_pkg_ctx *);

/* track packages already queued for installation, so cyclic or
 * duplicate (r/p)depends are only fetched/merged once per run */
static set *_qmerge_processed_pkgs = NULL;
static void pkg_merge(int, const depend_atom *, tree_pkg_ctx *);
static bool pkg_download(tree_pkg_ctx *);
static void qm_apply_moves_all(void);
static void qm_apply_news_all(void);
static int unmerge_packages(set *);

/* QMERGE_BLOCKERS soft-blocker auto-unmerge: installed pkgs (cat/PF) the
 * plan soft-blocks, collected during the conflict scan, unmerged before
 * the merge.  NULL/empty when the feature is off or nothing to drop. */
static set *qm_soft_unmerge = NULL;
static int pkg_unmerge(tree_pkg_ctx *, depend_atom *, set *, int, char **, int, char **);

static bool
qmerge_prompt(const char *p)
{
	printf("%s? [Y/n] ", p);
	fflush(stdout);
	switch (fgetc(stdin)) {
		case '\n':
		case 'y':
		case 'Y':
			return true;
		default:
			return false;
	}
}

/* propagate PKGDIR's gid and group mode bits onto files (0060) and
 * directories (02070, incl. setgid) created inside it, mirroring
 * portage's bintree._file_permissions/_ensure_dir: ownership is
 * inherited from the directory, never hardcoded */
static void
binpkg_perms(const char *path, bool isdir)
{
	char        pdir[_Q_PATH_MAX];
	struct stat pst;
	struct stat st;
	mode_t      mask = isdir ? 02070 : 0060;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	if (stat(pdir, &pst) != 0)
		return;
	if (chown(path, (uid_t)-1, pst.st_gid) != 0) {
		/* unprivileged callers cannot change the group; portage
		 * behaves the same way (apply_permissions best-effort) */
	}
	if (stat(path, &st) == 0)
		(void)chmod(path, (st.st_mode & 07777 & (mode_t)~mask) |
					(pst.st_mode & mask));
}

/* apply binpkg_perms to every directory component below PKGDIR */
static void
binpkg_tree_perms(const char *path)
{
	char        buf[_Q_PATH_MAX];
	char        pdir[_Q_PATH_MAX];
	size_t      plen;
	char       *p;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	plen = strlen(pdir);
	if (strncmp(path, pdir, plen) != 0)
		return;
	snprintf(buf, sizeof(buf), "%s", path);
	for (p = buf + plen; (p = strchr(p, '/')) != NULL; p++) {
		*p = '\0';
		binpkg_perms(buf, true);
		*p = '/';
	}
	binpkg_perms(buf, true);
}

/* GLEP 23 license visibility (portage-faithful hybrid): a package is
 * merge-visible when every required license is accepted.  Empty LICENSE
 * accepts (nothing to accept); an unaccepted license, or an @GROUP that
 * cannot be expanded (missing license_groups), blocks.  ACCEPT_LICENSE
 * is incremental; @GROUP references expand recursively; package.license
 * extends the set per atom. */
struct lic_acc {
	set  *acc;         /* explicitly accepted licenses */
	set  *den;         /* explicitly denied (after a wildcard) */
	bool  accept_all;  /* a bare '*' was in effect */
	set  *use;         /* the binpkg's enabled USE flags */
};

static void
lic_expand_group(const char *group, set *target, set *seen)
{
	const char *val;
	char       *tmp;
	char       *tok;
	char       *sp;

	if (contains_set(group, seen) != NULL)
		return;                       /* cycle guard */
	add_set_unique(group, seen, NULL);

	val = license_groups != NULL ? get_set(group, license_groups) : NULL;
	if (val == NULL) {
		static set *warned = NULL;

		if (warned == NULL)
			warned = create_set();
		if (contains_set(group, warned) == NULL) {
			warn("undefined license group '@%s'", group);
			add_set_unique(group, warned, NULL);
		}
		return;                       /* unexpandable -> contributes nothing */
	}
	tmp = xstrdup(val);
	for (tok = strtok_r(tmp, " \t", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t", &sp))
	{
		if (tok[0] == '@')
			lic_expand_group(tok + 1, target, seen);
		else if (tok[0] == '-')
			;                         /* invalid negated member, skip */
		else
			add_set_unique(tok, target, NULL);
	}
	free(tmp);
}

static void
lic_add_tokens(const char *str, struct lic_acc *la)
{
	char *tmp;
	char *tok;
	char *sp;
	bool  ign;

	if (str == NULL || str[0] == '\0')
		return;
	tmp = xstrdup(str);
	for (tok = strtok_r(tmp, " \t", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t", &sp))
	{
		bool        neg  = tok[0] == '-';
		const char *name = neg ? tok + 1 : tok;

		if (strcmp(name, "*") == 0) {
			if (neg) {                /* -* : reset everything */
				free_set(la->acc);
				free_set(la->den);
				la->acc = create_set();
				la->den = create_set();
				la->accept_all = false;
			} else {
				la->accept_all = true;
			}
			continue;
		}
		if (name[0] == '@') {
			set *seen = create_set();

			lic_expand_group(name + 1, neg ? la->den : la->acc, seen);
			free_set(seen);
			continue;
		}
		if (neg) {
			(void)del_set(name, la->acc, &ign);
			add_set_unique(name, la->den, NULL);
		} else {
			(void)del_set(name, la->den, &ign);
			add_set_unique(name, la->acc, NULL);
		}
	}
	free(tmp);
}

static bool
lic_leaf_ok(const char *name, struct lic_acc *la)
{
	if (contains_set(name, la->acc) != NULL)
		return true;
	if (la->accept_all && contains_set(name, la->den) == NULL)
		return true;
	return false;
}

static bool lic_parse_and(char **t, size_t n, size_t *i, struct lic_acc *la);

static bool
lic_parse_or(char **t, size_t n, size_t *i, struct lic_acc *la)
{
	bool any = false;

	while (*i < n && strcmp(t[*i], ")") != 0) {
		bool e;

		/* one element, mirroring lic_parse_and's element rule */
		if (strcmp(t[*i], "||") == 0) {
			(*i)++;
			if (*i < n && strcmp(t[*i], "(") == 0) (*i)++;
			e = lic_parse_or(t, n, i, la);
			if (*i < n && strcmp(t[*i], ")") == 0) (*i)++;
		} else if (strcmp(t[*i], "(") == 0) {
			(*i)++;
			e = lic_parse_and(t, n, i, la);
			if (*i < n && strcmp(t[*i], ")") == 0) (*i)++;
		} else {
			size_t L = strlen(t[*i]);

			if (L > 0 && t[*i][L - 1] == '?') {
				bool        neg = t[*i][0] == '!';
				char        flag[256];
				bool        active;

				snprintf(flag, sizeof(flag), "%.*s",
						 (int)(L - 1 - (neg ? 1 : 0)),
						 t[*i] + (neg ? 1 : 0));
				active = contains_set(flag, la->use) != NULL;
				if (neg) active = !active;
				(*i)++;
				if (*i < n && strcmp(t[*i], "(") == 0) (*i)++;
				{
					bool g = lic_parse_and(t, n, i, la);

					e = active ? g : true;
				}
				if (*i < n && strcmp(t[*i], ")") == 0) (*i)++;
			} else {
				e = lic_leaf_ok(t[*i], la);
				(*i)++;
			}
		}
		if (e)
			any = true;
	}
	return any;
}

static bool
lic_parse_and(char **t, size_t n, size_t *i, struct lic_acc *la)
{
	bool ok = true;

	while (*i < n && strcmp(t[*i], ")") != 0) {
		bool e;

		if (strcmp(t[*i], "||") == 0) {
			(*i)++;
			if (*i < n && strcmp(t[*i], "(") == 0) (*i)++;
			e = lic_parse_or(t, n, i, la);
			if (*i < n && strcmp(t[*i], ")") == 0) (*i)++;
		} else if (strcmp(t[*i], "(") == 0) {
			(*i)++;
			e = lic_parse_and(t, n, i, la);
			if (*i < n && strcmp(t[*i], ")") == 0) (*i)++;
		} else {
			size_t L = strlen(t[*i]);

			if (L > 0 && t[*i][L - 1] == '?') {
				bool neg = t[*i][0] == '!';
				char flag[256];
				bool active;

				snprintf(flag, sizeof(flag), "%.*s",
						 (int)(L - 1 - (neg ? 1 : 0)),
						 t[*i] + (neg ? 1 : 0));
				active = contains_set(flag, la->use) != NULL;
				if (neg) active = !active;
				(*i)++;
				if (*i < n && strcmp(t[*i], "(") == 0) (*i)++;
				{
					bool g = lic_parse_and(t, n, i, la);

					e = active ? g : true;
				}
				if (*i < n && strcmp(t[*i], ")") == 0) (*i)++;
			} else {
				e = lic_leaf_ok(t[*i], la);
				(*i)++;
			}
		}
		if (!e)
			ok = false;
	}
	return ok;
}

/* ACCEPT_LICENSE rejections collected during silent selection,
 * printed as a plan-time block like the USE rejects */
static set *qm_lic_rejects = NULL;

static bool
binpkg_license_ok(tree_pkg_ctx *pkg, atom_ctx *patom, bool silent)
{
	char          *lic = tree_pkg_meta(pkg, Q_LICENSE);
	char          *usestr;
	struct lic_acc la;
	char         **toks = NULL;
	size_t         ntok = 0;
	size_t         cap  = 0;
	size_t         i;
	char          *tmp;
	char          *tok;
	char          *sp;
	bool           ok;

	/* portage: empty LICENSE has nothing to accept -> visible */
	if (lic == NULL || lic[0] == '\0')
		return true;

	/* no ACCEPT_LICENSE at all (profile-less binhost consumer, e.g. a
	 * stage3 container with no repo synced): trust the binhost rather
	 * than mask the world, same philosophy as the keywords gate's
	 * no-arch-info fallback */
	if (accept_license == NULL || accept_license[0] == '\0')
		return true;

	la.acc = create_set();
	la.den = create_set();
	la.accept_all = false;
	la.use = create_set();

	/* the binpkg's fixed USE resolves the LICENSE conditionals */
	usestr = tree_pkg_meta(pkg, Q_USE);
	if (usestr != NULL) {
		tmp = xstrdup(usestr);
		for (tok = strtok_r(tmp, " \t\n", &sp);
			 tok != NULL;
			 tok = strtok_r(NULL, " \t\n", &sp))
			add_set_unique(tok, la.use, NULL);
		free(tmp);
	}

	/* global ACCEPT_LICENSE, then matching package.license entries */
	lic_add_tokens(accept_license, &la);
	if (pkg_license != NULL) {
		pkgcfg_t *pc;

		array_for_each(pkg_license, i, pc)
			if (atom_compare(patom, pc->atom) == EQUAL)
				lic_add_tokens(pc->vals, &la);
	}

	/* tokenise LICENSE (parens are separate, space-delimited tokens) */
	tmp = xstrdup(lic);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		if (ntok >= cap) {
			cap = cap > 0 ? cap * 2 : 16;
			toks = xrealloc(toks, sizeof(*toks) * cap);
		}
		toks[ntok++] = tok;
	}

	i  = 0;
	ok = lic_parse_and(toks, ntok, &i, &la);

	if (!ok) {
		/* name the specific unaccepted licenses (flat, approximate) */
		char   *masked = NULL;
		size_t  mlen   = 0;
		size_t  mcap   = 0;
		char   *ltext  = NULL;

		for (i = 0; i < ntok; i++) {
			size_t L = strlen(toks[i]);
			size_t o;

			if (strcmp(toks[i], "||") == 0 || strcmp(toks[i], "(") == 0 ||
					strcmp(toks[i], ")") == 0 ||
					(L > 0 && toks[i][L - 1] == '?'))
				continue;
			if (lic_leaf_ok(toks[i], &la))
				continue;
			if (mlen + L + 2 >= mcap) {
				mcap = (mlen + L + 2) * 2;
				masked = xrealloc(masked, mcap);
			}
			mlen += snprintf(masked + mlen, mcap - mlen, "%s%s",
							 mlen > 0 ? " " : "", toks[i]);
			/* best-effort pointer to the license text (GLEP 23):
			 * only when a repo checkout carries it, else skipped */
			for (o = 0; ltext == NULL && o < array_cnt(overlays); o++) {
				char *opath;

				xasprintf(&opath, "%s/licenses/%s",
						  (char *)array_get(overlays, o), toks[i]);
				if (access(opath, R_OK) == 0)
					ltext = opath;
				else
					free(opath);
			}
		}
		if (!silent) {
			warn("%s is masked by ACCEPT_LICENSE: license(s) not "
				 "accepted: %s (accept via ACCEPT_LICENSE or "
				 "package.license)",
				 atom_to_string(patom), masked != NULL ? masked : lic);
			if (ltext != NULL)
				warn("license text: %s", ltext);
		} else {
			/* selection-time rejection: collect for the plan-time
			 * ACCEPT_LICENSE block, bare cannot-satisfy explains
			 * nothing */
			char msg[1024];

			snprintf(msg, sizeof(msg), "=%s (licenses: %s)%s%s",
					 atom_to_string(patom),
					 masked != NULL ? masked : lic,
					 ltext != NULL ? " -- text: " : "",
					 ltext != NULL ? ltext : "");
			qm_lic_rejects = add_set_unique(msg, qm_lic_rejects, NULL);
		}
		free(masked);
		free(ltext);
	}

	free(tmp);
	free(toks);
	free_set(la.acc);
	free_set(la.den);
	free_set(la.use);
	return ok;
}

/* map the CHOST machine field to a Gentoo ARCH keyword; used only when
 * no profile provides ARCH (binhost-only consumer).  Returns NULL for an
 * unrecognised CHOST, in which case the caller trusts the binhost. */
static const char *
qm_arch_from_chost(const char *ch)
{
	if (ch == NULL || ch[0] == '\0')
		return NULL;

	if (strncmp(ch, "x86_64", 6) == 0 || strncmp(ch, "amd64", 5) == 0)
		return "amd64";
	if (ch[0] == 'i' && ch[1] >= '3' && ch[1] <= '6' &&
		strncmp(ch + 2, "86", 2) == 0)              /* i386..i686 */
		return "x86";
	if (strncmp(ch, "aarch64", 7) == 0)
		return "arm64";
	if (strncmp(ch, "arm", 3) == 0)
		return "arm";
	if (strncmp(ch, "powerpc64", 9) == 0)           /* incl. le */
		return "ppc64";
	if (strncmp(ch, "powerpc", 7) == 0 || strncmp(ch, "ppc", 3) == 0)
		return "ppc";
	if (strncmp(ch, "riscv", 5) == 0)
		return "riscv";
	if (strncmp(ch, "loongarch64", 11) == 0)
		return "loong";
	if (strncmp(ch, "s390", 4) == 0)
		return "s390";
	if (strncmp(ch, "sparc", 5) == 0)
		return "sparc";
	if (strncmp(ch, "mips", 4) == 0)
		return "mips";
	if (strncmp(ch, "alpha", 5) == 0)
		return "alpha";
	if (strncmp(ch, "hppa", 4) == 0 || strncmp(ch, "parisc", 6) == 0)
		return "hppa";
	if (strncmp(ch, "ia64", 4) == 0)
		return "ia64";
	if (strncmp(ch, "m68k", 4) == 0)
		return "m68k";
	return NULL;
}

/* effective ARCH for keyword matching: the profile/make.conf ARCH when
 * set, else derived from CHOST so a profile-less binhost consumer still
 * gets stable-vs-~testing gating.  NULL when neither is available. */
static const char *
qm_effective_arch(void)
{
	static const char *cached = NULL;
	static bool        done   = false;

	if (done)
		return cached;
	done = true;

	if (portarch != NULL && portarch[0] != '\0')
		cached = portarch;
	else
		cached = qm_arch_from_chost(chost);
	return cached;
}

/* GLEP 53 / PMS visibility: a package is visible when at least one of
 * its KEYWORDS matches the accepted set, built from the incremental
 * ACCEPT_KEYWORDS plus matching package.accept_keywords entries.
 * Wildcards per portage: `*` any stable arch, `~*` any testing arch,
 * `**` anything (including empty KEYWORDS). */
static bool
binpkg_keywords_ok(tree_pkg_ctx *pkg, atom_ctx *patom, bool silent)
{
	char   *kw  = tree_pkg_meta(pkg, Q_KEYWORDS);
	set    *acc = create_set();
	char   *tmp;
	char   *tok;
	char   *sp;
	size_t  i;
	bool    ok  = false;
	bool    ign;

	const char *earch = qm_effective_arch();

	/* no arch info at all (no profile, unrecognised CHOST) and no
	 * explicit ACCEPT_KEYWORDS: we cannot evaluate keywords, so trust
	 * the binhost to serve arch-appropriate packages rather than mask
	 * the whole world. */
	if ((earch == NULL || earch[0] == '\0') &&
		(accept_keywords == NULL || accept_keywords[0] == '\0')) {
		free_set(acc);
		return true;
	}

	/* global ACCEPT_KEYWORDS, incremental semantics in order; an
	 * empty result falls back to ARCH so a sparse config does not
	 * mask the whole world */
	tmp = xstrdup(accept_keywords != NULL &&
				  accept_keywords[0] != '\0' ? accept_keywords :
				  (earch != NULL ? earch : ""));
	for (tok = strtok_r(tmp, " \t", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t", &sp))
	{
		if (tok[0] == '-') {
			if (tok[1] == '*' && tok[2] == '\0') {
				free_set(acc);
				acc = create_set();
			} else {
				(void)del_set(tok + 1, acc, &ign);
			}
			continue;
		}
		add_set_unique(tok, acc, NULL);
	}
	free(tmp);

	/* matching package.accept_keywords entries extend the set; an
	 * entry without keywords means ~ARCH, like portage */
	if (pkg_accept_keywords != NULL) {
		pkgcfg_t *pc;

		array_for_each(pkg_accept_keywords, i, pc) {
			if (atom_compare(patom, pc->atom) != EQUAL)
				continue;
			if (pc->vals[0] == '\0') {
				char tilde[64];

				snprintf(tilde, sizeof(tilde), "~%s",
						 earch != NULL ? earch : "");
				add_set_unique(tilde, acc, NULL);
				continue;
			}
			tmp = xstrdup(pc->vals);
			for (tok = strtok_r(tmp, " \t", &sp);
				 tok != NULL;
				 tok = strtok_r(NULL, " \t", &sp))
			{
				if (tok[0] == '-') {
					if (tok[1] == '*' && tok[2] == '\0') {
						free_set(acc);
						acc = create_set();
					} else {
						(void)del_set(tok + 1, acc, &ign);
					}
					continue;
				}
				add_set_unique(tok, acc, NULL);
			}
			free(tmp);
		}
	}

	if (contains_set("**", acc) != NULL)
		ok = true;

	if (!ok && kw != NULL && kw[0] != '\0') {
		tmp = xstrdup(kw);
		for (tok = strtok_r(tmp, " \t\n", &sp);
			 tok != NULL && !ok;
			 tok = strtok_r(NULL, " \t\n", &sp))
		{
			if (tok[0] == '-')
				continue;   /* -arch / -*: never acceptable */
			if (contains_set(tok, acc) != NULL)
				ok = true;
			else if (tok[0] == '~' && contains_set("~*", acc) != NULL)
				ok = true;
			else if (tok[0] != '~' && contains_set("*", acc) != NULL)
				ok = true;
		}
		free(tmp);
	}

	if (!ok && !silent) {
		warn("%s is masked: no accepted keyword "
			 "(KEYWORDS=\"%s\" vs ACCEPT_KEYWORDS=\"%s\"); "
			 "add an entry to package.accept_keywords to override",
			 atom_to_string(patom),
			 kw != NULL ? kw : "<missing from binpkg metadata>",
			 accept_keywords != NULL ? accept_keywords : "");
	}

	free_set(acc);
	return ok;
}

/* -------- multi-binhost support (portage binrepos.conf parity) -----
 * repos come from /usr/share/portage/config/binrepos.conf, then
 * ${PORTAGE_CONFIGROOT}/etc/portage/binrepos.conf ([name] sections
 * with sync-uri = and optional priority =), and PORTAGE_BINHOST
 * entries are folded in as implicit repos, exactly like portage's
 * lib/portage/binrepo/config.py.  fetch() then walks the repos in
 * (priority, name) order, first successful download wins. */
struct qm_binrepo {
	char *name;
	char *uri;
	char *loc;        /* explicit location = from binrepos.conf, or NULL */
	int   priority;
	int   verify_sig; /* verify-signature =: 1 true, 0 false, -1 unset */
};
static struct qm_binrepo *qm_binrepos  = NULL;
static size_t             qm_nbinrepos = 0;

static void
binrepos_add(const char *name, const char *uri, const char *loc, int priority,
			 int verify_sig)
{
	size_t i;
	size_t len;
	char  *u;

	if (uri == NULL || *uri == '\0')
		return;

	u = xstrdup(uri);
	/* normalise: strip trailing slashes like portage does */
	len = strlen(u);
	while (len > 1 && u[len - 1] == '/')
		u[--len] = '\0';

	/* dedupe on sync-uri, first definition wins */
	for (i = 0; i < qm_nbinrepos; i++) {
		if (strcmp(qm_binrepos[i].uri, u) == 0) {
			free(u);
			return;
		}
	}

	qm_binrepos = xrealloc(qm_binrepos,
						   sizeof(*qm_binrepos) * (qm_nbinrepos + 1));
	qm_binrepos[qm_nbinrepos].name     = xstrdup(name);
	qm_binrepos[qm_nbinrepos].uri      = u;
	qm_binrepos[qm_nbinrepos].loc      =
			loc != NULL && *loc != '\0' ? xstrdup(loc) : NULL;
	qm_binrepos[qm_nbinrepos].priority = priority;
	qm_binrepos[qm_nbinrepos].verify_sig = verify_sig;
	qm_nbinrepos++;
}

/* effective store dir of repo i: explicit location =, else PKGDIR for
 * the primary (compat: single-binhost setups keep their cache), else
 * /var/cache/binhost/<name> (portage >=3.0.77 default) */
static const char *
qm_repo_loc(size_t i, char *buf, size_t buflen)
{
	if (qm_binrepos[i].loc != NULL)
		return qm_binrepos[i].loc;
	if (i == 0)
		return pkgdir;
	snprintf(buf, buflen, "/var/cache/binhost/%s", qm_binrepos[i].name);
	return buf;
}

static void
binrepos_load_file(const char *file)
{
	FILE   *fp;
	char   *line = NULL;
	size_t  len  = 0;
	char    name[128]      = "";
	char    uri[_Q_PATH_MAX] = "";
	char    loc[_Q_PATH_MAX] = "";
	int     priority       = 0;
	int     verify_sig     = -1;
	bool    insection      = false;

	fp = fopen(file, "r");
	if (fp == NULL)
		return;

	while (getline(&line, &len, fp) != -1) {
		char *s = rmspace(line);
		char *e;

		if (*s == '\0' || *s == '#' || *s == ';')
			continue;

		if (*s == '[') {
			/* flush previous section */
			if (insection) {
				if (strcmp(name, "DEFAULT") == 0)
					;  /* INI defaults section, not a repo */
				else if (uri[0] == '\0')
					warn("binrepo %s has no sync-uri, ignored", name);
				else
					binrepos_add(name, uri, loc, priority, verify_sig);
			}
			e = strchr(s, ']');
			if (e == NULL)
				continue;
			*e = '\0';
			snprintf(name, sizeof(name), "%s", s + 1);
			uri[0]     = '\0';
			loc[0]     = '\0';
			priority   = 0;
			verify_sig = -1;
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
		/* other keys (fetchcommand, frozen) are currently not used */
	}

	if (insection) {
		if (strcmp(name, "DEFAULT") == 0)
			;  /* INI defaults section, not a repo */
		else if (uri[0] == '\0')
			warn("binrepo %s has no sync-uri, ignored", name);
		else
			binrepos_add(name, uri, loc, priority, verify_sig);
	}

	free(line);
	fclose(fp);
}

/* binrepos.conf may be a plain file or, like most portage config
 * bits, a directory of files read in sorted order */
static void
binrepos_load_path(const char *path)
{
	struct dirent **dents;
	int             cnt;
	int             i;

	cnt = scandir(path, &dents, NULL, alphasort);
	if (cnt >= 0) {
		char sub[_Q_PATH_MAX * 2];

		for (i = 0; i < cnt; i++) {
			if (dents[i]->d_name[0] == '.')
				continue;
			snprintf(sub, sizeof(sub), "%s/%s",
					 path, dents[i]->d_name);
			binrepos_load_file(sub);
		}
		scandir_free(dents, cnt);
	} else {
		binrepos_load_file(path);
	}
}

static int
binrepos_cmp(const void *a, const void *b)
{
	const struct qm_binrepo *ra = a;
	const struct qm_binrepo *rb = b;

	if (ra->priority != rb->priority)
		return ra->priority - rb->priority;
	return strcmp(ra->name, rb->name);
}

static void
binrepos_load(void)
{
	static bool loaded = false;
	char        path[_Q_PATH_MAX];
	int         prio;
	char       *bh;
	char       *tok;
	char       *sp;
	int         n;

	if (loaded)
		return;
	loaded = true;

	snprintf(path, sizeof(path), "%s/%s", CONFIG_EPREFIX,
			 "usr/share/portage/config/binrepos.conf");
	binrepos_load_path(path);
	snprintf(path, sizeof(path), "%s/etc/portage/binrepos.conf",
			 configroot);
	binrepos_load_path(path);

	/* fold PORTAGE_BINHOST entries in as implicit repos, reversed,
	 * with incrementing priority (after explicit default 0) */
	prio = 0;
	bh = xstrdup(binhost);
	/* count and walk in reverse like portage does */
	{
		char **uris = NULL;
		n = 0;
		for (tok = strtok_r(bh, " \t", &sp);
			 tok != NULL;
			 tok = strtok_r(NULL, " \t", &sp))
		{
			uris = xrealloc(uris, sizeof(char *) * (n + 1));
			uris[n++] = tok;
		}
		while (n-- > 0) {
			char iname[64];
			snprintf(iname, sizeof(iname), "binhost%d", ++prio);
			binrepos_add(iname, uris[n], NULL, prio, -1);
		}
		free(uris);
	}
	free(bh);

	if (qm_nbinrepos > 1)
		qsort(qm_binrepos, qm_nbinrepos, sizeof(*qm_binrepos),
			  binrepos_cmp);
}

/* undo make.globals-style backslash escaping (\$ \" \\) so the
 * FETCHCOMMAND template can be re-evaluated by the spawned shell */
static char *
unescape_fetchcommand(const char *s)
{
	char       *out = xstrdup(s);
	char       *w   = out;
	const char *r;

	for (r = s; *r != '\0'; r++) {
		if (*r == '\\' &&
				(r[1] == '$' || r[1] == '"' || r[1] == '\\'))
			continue;  /* drop the escape, keep the escaped char */
		*w++ = *r;
	}
	*w = '\0';
	return out;
}

/* If-Modified-Since threshold for the next fetch (0 = off) and the
 * matching 304-not-modified out-flag */
static time_t qm_fetch_ims    = 0;
static bool   qm_fetch_notmod = false;

/* in-process download via libcurl; resumes partial files */
static int
fetch_curl(const char *repo_uri, const char *destdir, const char *src)
{
	static bool curl_ready = false;
	const char *base;
	char       *uri;
	char       *dest;
	FILE       *out;
	CURL       *curl;
	CURLcode    res;
	curl_off_t  resume_from = 0;
	struct stat st;

	if (!curl_ready) {
		curl_global_init(CURL_GLOBAL_DEFAULT);
		curl_ready = true;
	}

	base = strrchr(src, '/');
	base = base != NULL ? base + 1 : src;
	xasprintf(&uri, "%s/%s", repo_uri, src);
	xasprintf(&dest, "%s/%s", destdir, base);

	if (stat(dest, &st) == 0 && S_ISREG(st.st_mode))
		resume_from = (curl_off_t)st.st_size;

	if (pretend) {
		printf("fetch %s -> %s\n", uri, dest);
		free(uri);
		free(dest);
		return 0;
	}

	out = fopen(dest, resume_from > 0 ? "ab" : "wb");
	if (out == NULL) {
		warnp("cannot open %s for writing", dest);
		free(uri);
		free(dest);
		return -1;
	}

	curl = curl_easy_init();
	if (curl == NULL) {
		warn("failed to init curl");
		fclose(out);
		free(uri);
		free(dest);
		return -1;
	}
	curl_easy_setopt(curl, CURLOPT_URL, uri);
	curl_easy_setopt(curl, CURLOPT_WRITEDATA, out);
	curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
	curl_easy_setopt(curl, CURLOPT_FAILONERROR, 1L);
	curl_easy_setopt(curl, CURLOPT_RESUME_FROM_LARGE, resume_from);
	curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, 60L);
	curl_easy_setopt(curl, CURLOPT_USERAGENT,
					 "portage-utils qmerge binpkg-fetch");
	curl_easy_setopt(curl, CURLOPT_NOPROGRESS,
					 (quiet || !verbose) ? 1L : 0L);
	/* index refresh: only download when newer than the cached copy */
	qm_fetch_notmod = false;
	if (qm_fetch_ims > 0) {
		curl_easy_setopt(curl, CURLOPT_TIMECONDITION,
						 (long)CURL_TIMECOND_IFMODSINCE);
		curl_easy_setopt(curl, CURLOPT_TIMEVALUE, (long)qm_fetch_ims);
	}
	res = curl_easy_perform(curl);
	{
		long code = 0;
		curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &code);
		if (res == CURLE_HTTP_RETURNED_ERROR && code == 416)
			res = CURLE_OK;   /* range not satisfiable: already complete */
	}
	if (qm_fetch_ims > 0) {
		long unmet = 0;

		curl_easy_getinfo(curl, CURLINFO_CONDITION_UNMET, &unmet);
		if (unmet != 0)
			qm_fetch_notmod = true;
	}
	curl_easy_cleanup(curl);
	fclose(out);
	/* Moves, News.tar and Packages.gz are optional files: a binhost
	 * without them is normal, so their fetch failures stay silent */
	if (res != CURLE_OK && !qm_fetch_notmod &&
			strcmp(src, "Moves") != 0 && strcmp(src, "News.tar") != 0 &&
			strcmp(src, "Packages.gz") != 0)
		warn("fetching %s failed: %s", uri, curl_easy_strerror(res));
	free(uri);
	free(dest);
	return res == CURLE_OK ? 0 : -1;
}

/* fetch src from the single repo i into destdir; 0 = a non-empty file
 * landed */
static int
fetch_repo(size_t i, const char *destdir, const char *src)
{
	const char *uri = qm_binrepos[i].uri;
	const char *base;
	char       *dest;
	struct stat st;
	int         ret = -1;

	fflush(NULL);

	base = strrchr(src, '/');
	base = base != NULL ? base + 1 : src;
	xasprintf(&dest, "%s/%s", destdir, base);

	if (qfetchcommand[0] != '\0') {
		/* qmerge-specific fetcher: when QFETCHCOMMAND is set in
		 * make.conf/env, spawn it (same portage template grammar:
		 * ${DISTDIR} ${URI} ${FILE}), exporting the vars it refers
		 * to; failures are tolerated so the next repo can be tried.
		 * Empty (the default) -> built-in libcurl.  Deliberately NOT
		 * portage's FETCHCOMMAND, so make.globals' wget default does
		 * not drag wget in. */
		char *cmd;
		char *script;

		if (qresumecommand[0] != '\0' &&
				stat(dest, &st) == 0 && st.st_size > 0)
			cmd = unescape_fetchcommand(qresumecommand);
		else
			cmd = unescape_fetchcommand(qfetchcommand);

		xasprintf(&script,
				"(export DISTDIR='%s' URI='%s/%s' FILE='%s'; %s%s) || :",
				destdir, uri, src, base,
				pretend ? "echo " : "", cmd);
		xsystem(script, AT_FDCWD);
		free(script);
		free(cmd);
	} else {
		/* no external fetch tool configured: built-in libcurl */
		(void)fetch_curl(uri, destdir, src);
	}

	if (!pretend && stat(dest, &st) == 0 && st.st_size > 0) {
		binpkg_perms(dest, false);
		ret = 0;
	}

	free(dest);

	fflush(stdout);
	fflush(stderr);
	return ret;
}

static void
fetch(const char *destdir, const char *src)
{
	static bool warned = false;
	const char *base;
	size_t      i;

	binrepos_load();
	if (qm_nbinrepos == 0) {
		if (!warned) {
			warn("no binhosts configured "
				 "(binrepos.conf missing and PORTAGE_BINHOST unset)");
			warned = true;
		}
		return;
	}

	base = strrchr(src, '/');
	base = base != NULL ? base + 1 : src;

	/* walk the repos in priority order until one delivers */
	for (i = 0; i < qm_nbinrepos; i++) {
		if (fetch_repo(i, destdir, src) == 0)
			break;

		if (pretend)  /* show every candidate in fallback order */
			continue;

		if (i + 1 < qm_nbinrepos)
			warn("%s not available on binhost %s, trying %s",
				 base, qm_binrepos[i].name, qm_binrepos[i + 1].name);
	}
}

/* QMERGE_MOVES policy (make.conf/env): which move-directive source
 * applies when both a repo checkout and fetched Moves files exist.
 * repo (default) = repo profiles/updates win, fetched Moves fallback
 * binhost        = fetched Moves win, repo fallback
 * repo-only / binhost-only = that single source, no fallback
 * none           = moves machinery off entirely */
enum qm_mvpol {
	QM_MV_REPO,
	QM_MV_BINHOST,
	QM_MV_REPO_ONLY,
	QM_MV_BINHOST_ONLY,
	QM_MV_NONE
};

static enum qm_mvpol
qm_moves_policy(void)
{
	const char *v = qmerge_moves_conf;

	if (v == NULL || v[0] == '\0' || strcmp(v, "repo") == 0)
		return QM_MV_REPO;
	if (strcmp(v, "binhost") == 0 || strcmp(v, "moves") == 0)
		return QM_MV_BINHOST;
	if (strcmp(v, "repo-only") == 0)
		return QM_MV_REPO_ONLY;
	if (strcmp(v, "binhost-only") == 0 || strcmp(v, "moves-only") == 0)
		return QM_MV_BINHOST_ONLY;
	if (strcmp(v, "none") == 0 || strcmp(v, "off") == 0 ||
			strcmp(v, "false") == 0)
		return QM_MV_NONE;
	warn("unknown QMERGE_MOVES value '%s', using 'repo'", v);
	return QM_MV_REPO;
}

/* a cached index younger than its own TTL header needs no refetch;
 * QMERGE_IGNORE_TTL=1 forces (portage bintree TTL semantics, with
 * the store file's mtime as the download timestamp) */
static bool
qm_index_fresh(const char *loc)
{
	char        path[_Q_PATH_MAX + 16];
	struct stat st;
	FILE       *f;
	char        line[256];
	long        ttl = 0;

	if (getenv("QMERGE_IGNORE_TTL") != NULL)
		return false;
	snprintf(path, sizeof(path), "%s%s/%s", portroot, loc, Packages);
	if (stat(path, &st) != 0 || st.st_size == 0)
		return false;
	f = fopen(path, "r");
	if (f == NULL)
		return false;
	/* the header block ends at the first blank line */
	while (fgets(line, sizeof(line), f) != NULL) {
		if (line[0] == '\n')
			break;
		if (strncmp(line, "TTL: ", 5) == 0) {
			ttl = atol(line + 5);
			break;
		}
	}
	fclose(f);
	if (ttl <= 0)
		return false;
	return time(NULL) < st.st_mtime + ttl;
}

static bool
qm_gunzip_file(const char *src, const char *dst)
{
	gzFile in  = gzopen(src, "rb");
	FILE  *out = in != NULL ? fopen(dst, "w") : NULL;
	char   gbuf[BUFSIZ];
	int    n   = 0;
	bool   ok  = out != NULL;

	while (ok && (n = gzread(in, gbuf, sizeof(gbuf))) > 0)
		if (fwrite(gbuf, 1, (size_t)n, out) != (size_t)n)
			ok = false;
	if (n < 0)
		ok = false;
	if (in != NULL)
		gzclose(in);
	if (out != NULL)
		fclose(out);
	if (!ok)
		unlink(dst);
	return ok;
}

static void
qmerge_initialize(void)
{
	char *buf;

	if (strlen(BUSYBOX) > 0)
		if (access(BUSYBOX, X_OK) != 0)
			err(BUSYBOX " must be installed");

	if (access("/bin/sh", X_OK) != 0)
		err("/bin/sh must be installed");

	if (pkgdir[0] != '/')
		errf("PKGDIR='%s' does not appear to be valid", pkgdir);

	if (!search_pkgs && !pretend) {
		if (mkdir_p(pkgdir, 0755))
			errp("could not setup PKGDIR: %s", pkgdir);
	}

	xasprintf(&buf, "%s%s/portage/", portroot, port_tmpdir);
	mkdir_p(buf, 0755);
	xchdir(buf);

	if (force_download == 1 /* -f: fetch */) {
		struct stat st;
		size_t      i;
		char        locbuf[_Q_PATH_MAX];

		binrepos_load();
		if (qm_nbinrepos == 0)
			warn("no binhosts configured "
				 "(binrepos.conf missing and PORTAGE_BINHOST unset)");

		/* every repo gets its own index, fetched into the tempdir
		 * first so the existing one in the store survives a failed
		 * fetch; per-repo failure is not fatal */
		for (i = 0; i < qm_nbinrepos; i++) {
			const char *loc = qm_repo_loc(i, locbuf, sizeof(locbuf));
			char        spath[_Q_PATH_MAX + 16];
			struct stat sst;
			bool        fetched = false;

			/* a cached index younger than its TTL header is current */
			if (qm_index_fresh(loc)) {
				if (!quiet)
					printf(">>> Packages index from %s is fresh (TTL)\n",
						   qm_binrepos[i].name);
				continue;
			}

			unlink(Packages);
			unlink("Packages.gz");
			if (!quiet)
				printf(">>> Fetching Packages index from %s\n",
					   qm_binrepos[i].name);

			/* If-Modified-Since from the cached copy's fetch time */
			snprintf(spath, sizeof(spath), "%s%s/%s",
					 portroot, loc, Packages);
			qm_fetch_ims = stat(spath, &sst) == 0 ? sst.st_mtime : 0;

			/* compressed index preferred (portage tries .gz first) */
			if (fetch_repo(i, buf, "Packages.gz") == 0) {
				char gzp[_Q_PATH_MAX + 16];
				char plp[_Q_PATH_MAX + 16];

				snprintf(gzp, sizeof(gzp), "%s/Packages.gz", buf);
				snprintf(plp, sizeof(plp), "%s/%s", buf, Packages);
				if (qm_gunzip_file(gzp, plp))
					fetched = true;
				else
					warn("corrupt Packages.gz from %s, trying plain",
						 qm_binrepos[i].name);
				unlink(gzp);
			}
			if (!fetched && !qm_fetch_notmod &&
					fetch_repo(i, buf, Packages) == 0)
				fetched = true;
			qm_fetch_ims = 0;
			if (!fetched) {
				if (qm_fetch_notmod) {
					if (!quiet)
						printf(">>> Packages index from %s is up "
							   "to date\n", qm_binrepos[i].name);
				} else if (!pretend) {
					warn("no Packages index from binhost %s, "
						 "keeping previous", qm_binrepos[i].name);
				}
				continue;
			}

			if (!pretend && stat(Packages, &st) == 0 && st.st_size > 0) {
				char *pdir;
				int   sfd;
				int   dfd;

				xasprintf(&pdir, "%s%s", portroot, loc);
				if (mkdir_p(pdir, 0755) != 0 ||
						(dfd = open(pdir, O_RDONLY | O_CLOEXEC)) < 0)
				{
					warnp("cannot open %s, keeping previous Packages index",
						  pdir);
				}
				else
				{
					sfd = open(buf, O_RDONLY | O_CLOEXEC);
					if (sfd < 0 ||
							move_file(sfd, Packages, dfd, Packages,
									  NULL) != 0) {
						warnp("failed to move fresh Packages index into %s",
							  pdir);
					} else {
						char ppath[_Q_PATH_MAX + 16];

						snprintf(ppath, sizeof(ppath), "%s/%s",
								 pdir, Packages);
						binpkg_perms(ppath, false);
					}
					if (sfd >= 0)
						close(sfd);
					close(dfd);
				}
				free(pdir);
			}

			/* optional news transport: News.tar next to Packages;
			 * opt-in via QNEWS_ENABLE in make.conf/env */
			unlink("News.tar");
			if (qnews_enable &&
					fetch_repo(i, buf, "News.tar") == 0 &&
					!pretend && stat("News.tar", &st) == 0 &&
					st.st_size > 0) {
				char *ndir2;
				int   ndfd;
				int   nsfd;

				xasprintf(&ndir2, "%s%s", portroot, loc);
				if (mkdir_p(ndir2, 0755) == 0 &&
						(ndfd = open(ndir2, O_RDONLY | O_CLOEXEC)) >= 0) {
					nsfd = open(buf, O_RDONLY | O_CLOEXEC);
					if (nsfd >= 0) {
						if (move_file(nsfd, "News.tar", ndfd,
									  "News.tar", NULL) != 0)
							warnp("failed to move fresh News.tar into %s",
								  ndir2);
						close(nsfd);
					}
					close(ndfd);
				}
				free(ndir2);
			}

			/* optional package-moves transport: a Moves file next to
			 * Packages on the binhost (missing = no moves, no error);
			 * skipped when the policy never consumes the fetched form */
			unlink("Moves");
			if (qm_moves_policy() != QM_MV_NONE &&
					qm_moves_policy() != QM_MV_REPO_ONLY &&
					fetch_repo(i, buf, "Moves") == 0 &&
					!pretend && stat("Moves", &st) == 0 && st.st_size > 0) {
				char *mdir;
				int   mdfd;
				int   msfd;

				xasprintf(&mdir, "%s%s", portroot, loc);
				if (mkdir_p(mdir, 0755) == 0 &&
						(mdfd = open(mdir, O_RDONLY | O_CLOEXEC)) >= 0) {
					msfd = open(buf, O_RDONLY | O_CLOEXEC);
					if (msfd >= 0) {
						if (move_file(msfd, "Moves", mdfd, "Moves",
									  NULL) != 0)
							warnp("failed to move fresh Moves into %s",
								  mdir);
						close(msfd);
					}
					close(mdfd);
				}
				free(mdir);
			}
		}

		if (!pretend) {
			qm_apply_moves_all();
			qm_apply_news_all();
		}
	}

	free(buf);
}

static tree_ctx *_qmerge_vdb_tree    = NULL;
/* one binpkg tree per binrepo store (parallel to qm_binrepos, or a
 * single PKGDIR tree when no repos are configured); repos sharing a
 * store share the ctx pointer */
static tree_ctx **qm_bintrees  = NULL;
static size_t     qm_nbintrees = 0;

static size_t
qm_bintree_cnt(void)
{
	binrepos_load();
	return qm_nbinrepos > 0 ? qm_nbinrepos : 1;
}

static tree_ctx *
qm_bintree(size_t i)
{
	char        locbuf[_Q_PATH_MAX];
	const char *loc;
	size_t      j;

	if (qm_bintrees == NULL) {
		qm_nbintrees = qm_bintree_cnt();
		qm_bintrees  = xzalloc(sizeof(*qm_bintrees) * qm_nbintrees);
	}
	if (i >= qm_nbintrees)
		return NULL;
	if (qm_bintrees[i] != NULL)
		return qm_bintrees[i];

	loc = qm_nbinrepos > 0 ?
			qm_repo_loc(i, locbuf, sizeof(locbuf)) : pkgdir;

	for (j = 0; j < i; j++) {
		char        lb2[_Q_PATH_MAX];
		const char *l2 = qm_nbinrepos > 0 ?
				qm_repo_loc(j, lb2, sizeof(lb2)) : pkgdir;

		if (qm_bintrees[j] != NULL && strcmp(loc, l2) == 0) {
			qm_bintrees[i] = qm_bintrees[j];
			return qm_bintrees[i];
		}
	}

	qm_bintrees[i] = tree_new(portroot, loc, TREETYPE_BINPKG, true);
	return qm_bintrees[i];
}

/* which repo (index into qm_binrepos) advertised this pkg; -1 unknown */
static ssize_t
qm_repoidx_of_pkg(tree_pkg_ctx *pkg)
{
	tree_ctx *t = tree_pkg_get_tree(pkg);
	size_t    i;

	for (i = 0; i < qm_nbintrees; i++)
		if (qm_bintrees[i] == t)
			return (ssize_t)i;
	return -1;
}

static const char *
qm_repo_name_of_pkg(tree_pkg_ctx *pkg)
{
	ssize_t i = qm_repoidx_of_pkg(pkg);

	if (i < 0 || qm_nbinrepos == 0)
		return NULL;
	return qm_binrepos[i].name;
}

/* repo tag colour: #a0522d (sienna) as 24-bit escape; bold variant for
 * explicitly requested targets (emerge bolds its world entries the same
 * way); empty when the global colour state says no colour */
static const char *
qm_repo_tag_color_b(bool boldtag)
{
	if (*NORM == '\0')
		return "";
	return boldtag ? "\033[01;38;2;160;82;45m" : "\033[38;2;160;82;45m";
}
#define qm_repo_tag_color() qm_repo_tag_color_b(false)

/* emerge's keyword column for the plan: "" = stable for ARCH, "~" =
 * only the testing keyword, "**" = no keyword for ARCH at all (the
 * pkg was accepted by other means, e.g. package.accept_keywords) */
static const char *
qm_keyword_marker(tree_pkg_ctx *pkg)
{
	char       *kw    = tree_pkg_meta(pkg, Q_KEYWORDS);
	const char *earch = qm_effective_arch();
	char       *tmp;
	char       *tok;
	char       *sp;
	bool        testing = false;

	if (earch == NULL || earch[0] == '\0')
		return "";
	if (kw == NULL || *kw == '\0')
		return "**";

	tmp = xstrdup(kw);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		if (strcmp(tok, earch) == 0) {
			free(tmp);
			return "";
		}
		if (tok[0] == '~' && strcmp(tok + 1, earch) == 0)
			testing = true;
	}
	free(tmp);
	return testing ? "~" : "**";
}

/* is this resolved package one the user asked for on the command line
 * (emerge world-style bold), rather than a pulled-in dependency?
 * todo entries may be bare names ("epkg"), cat/pn or versioned atoms */
static bool
qm_atom_is_target(const depend_atom *pa, set *todo)
{
	array  *keys;
	size_t  n;
	char   *t;
	bool    ret = false;

	if (todo == NULL || pa == NULL || pa->PN == NULL)
		return false;

	keys = set_keys(todo);
	array_for_each(keys, n, t) {
		depend_atom *ta = atom_explode(t);

		if (ta == NULL)
			continue;
		if (ta->PN != NULL && strcmp(ta->PN, pa->PN) == 0 &&
				(ta->CATEGORY == NULL ||
				 (pa->CATEGORY != NULL &&
				  strcmp(ta->CATEGORY, pa->CATEGORY) == 0)))
			ret = true;
		atom_implode(ta);
		if (ret)
			break;
	}
	array_free(keys);
	return ret;
}
#define BV_INSTALLED BV_VDB
#define BV_BINARY    BV_BINPKG
#define BV_EBUILD    (1<<0)  /* not yet supported */
#define BV_VDB       (1<<1)
#define BV_BINPKG    (1<<2)

/* is this cpv package.mask'd?  package_masks (profile cascade + /etc/portage)
 * is keyed by the raw mask-atom STRING, so index it once into cat/pn -> atoms
 * (like qkeyword does) and match the cpv against that pkg's mask atoms.  Empty
 * (e.g. no profile on a pure binhost box) = never masked.  (package.unmask
 * override not yet parsed, deferred.) */
/* cat/pn -> array of mask/unmask atoms; lazy */
static hash_t *_binpkg_pmasks   = NULL;
static hash_t *_binpkg_punmasks = NULL;

static hash_t *
binpkg_mask_index(hash_t *src)
{
	hash_t *idx = hash_new();
	array  *keys;
	size_t  i;
	char   *mask;

	if (src == NULL)
		return idx;
	keys = hash_keys(src);
	array_for_each(keys, i, mask) {
		depend_atom *a = atom_explode(mask);
		array       *b;
		array       *eb;

		if (a == NULL)
			continue;
		b = array_new();
		array_append(b, a);
		hash_add(idx, atom_format("%[CAT]%[PN]", a), b, (void **)&eb);
		/* hash_add REPLACES the stored value and returns the previous
		 * one: the hash now holds b, so merge the old bucket into it */
		if (eb != NULL) {
			size_t       j;
			depend_atom *pa;

			array_for_each(eb, j, pa)
				array_append(b, pa);
			array_free(eb);
		}
	}
	array_free(keys);
	return idx;
}

static bool
binpkg_masked(const depend_atom *patom)
{
	array       *bucket;
	size_t       n;
	depend_atom *m;
	bool         masked = false;

	if (package_masks == NULL || patom == NULL)
		return false;

	if (_binpkg_pmasks == NULL)
		_binpkg_pmasks = binpkg_mask_index(package_masks);
	if (_binpkg_punmasks == NULL)
		_binpkg_punmasks = binpkg_mask_index(package_unmasks);

	bucket = hash_get(_binpkg_pmasks, atom_format("%[CAT]%[PN]", patom));
	if (bucket == NULL)
		return false;
	array_for_each(bucket, n, m)
		if (atom_compare(patom, m) == EQUAL) {
			masked = true;
			break;
		}
	if (!masked)
		return false;

	/* package.unmask overrides a matching mask; qmerge pools profile
	 * and /etc/portage masks, so unmask overrides both */
	bucket = hash_get(_binpkg_punmasks, atom_format("%[CAT]%[PN]", patom));
	if (bucket != NULL)
		array_for_each(bucket, n, m)
			if (atom_compare(patom, m) == EQUAL)
				return false;
	return true;
}

/* --binpkg-respect-use: -1 default (gate foreign repos only, the
 * multi-binhost skew protection), 1 gate all repos incl local, 0 off.
 * portage's own -K mode defaults this OFF (no source fallback), so
 * gating the local repo is opt-in. */
static char qm_respect_use = -1;

/* --usepkg-exclude: atoms never satisfied from binpkgs.  portage falls
 * back to a source build for these; qmerge has no ebuilds, so an atom
 * only an excluded binpkg can satisfy refuses at resolve time. */
static array      *qm_usepkg_excl     = NULL;
static const char *qm_usepkg_excl_src = NULL;
static char        qm_excl_live       = 0;

static void
qm_parse_usepkg_exclude(const char *arg, const char *src)
{
	char *tmp = xstrdup(arg);
	char *tok;
	char *sp;

	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		depend_atom *a = atom_explode(tok);

		if (a == NULL) {
			warn("invalid atom in %s: %s", src, tok);
			continue;
		}
		if (qm_usepkg_excl == NULL)
			qm_usepkg_excl = array_new();
		array_append(qm_usepkg_excl, a);
	}
	free(tmp);
	qm_usepkg_excl_src = src;
}

static bool
binpkg_excluded(tree_pkg_ctx *pkg, depend_atom *patom, bool silent)
{
	size_t       n;
	depend_atom *x;

	if (qm_usepkg_excl != NULL && patom != NULL) {
		array_for_each(qm_usepkg_excl, n, x)
			if (atom_compare(patom, x) == EQUAL) {
				if (!silent) {
					char exs[256];

					/* atom_to_string shares a static buffer: copy out */
					snprintf(exs, sizeof(exs), "%s", atom_to_string(x));
					warn("%s is excluded by %s (%s) -- refusing",
						 atom_to_string(patom), qm_usepkg_excl_src, exs);
				}
				return true;
			}
	}

	if (qm_excl_live && pkg != NULL) {
		char *props = tree_pkg_meta(pkg, Q_PROPERTIES);

		if (props != NULL && props[0] != '\0') {
			char *tmp  = xstrdup(props);
			char *tok;
			char *sp;
			bool  live = false;

			for (tok = strtok_r(tmp, " \t\n", &sp);
				 tok != NULL;
				 tok = strtok_r(NULL, " \t\n", &sp))
				if (strcmp(tok, "live") == 0) {
					live = true;
					break;
				}
			free(tmp);
			if (live) {
				if (!silent)
					warn("%s is a live package -- refusing per "
						 "--usepkg-exclude-live", atom_to_string(patom));
				return true;
			}
		}
	}

	return false;
}

/* cannot-satisfy diagnostic: name the exclude atom that hid the
 * candidates, so an env-driven exclusion is traceable */
static const char *
qm_excl_hint(const depend_atom *atom)
{
	static char  hint[320];
	size_t       n;
	depend_atom *x;

	if (qm_usepkg_excl == NULL || atom == NULL || atom->PN == NULL)
		return "";
	array_for_each(qm_usepkg_excl, n, x) {
		if (x->PN == NULL || strcmp(atom->PN, x->PN) != 0)
			continue;
		if (atom->CATEGORY != NULL && x->CATEGORY != NULL &&
				strcmp(atom->CATEGORY, x->CATEGORY) != 0)
			continue;
		snprintf(hint, sizeof(hint), " (%s excluded by %s)",
				 atom_to_string(x), qm_usepkg_excl_src);
		return hint;
	}
	return "";
}

/* package moves: portage profiles/updates directives, fetched from the
 * binhost as <store>/Moves (the repo-less transport, published next to
 * Packages).  Applied to VDB + world during -f; the applied content is
 * kept in <store>/.moves-applied so a directive set runs once.
 * a1 = move old cat/pn, or slotmove atom
 * a2 = move new cat/pn, or slotmove old slot
 * a3 = slotmove new slot */
struct qm_move {
	bool  slotmove;
	char *a1;
	char *a2;
	char *a3;
};

static void
qm_moves_free(array *mv)
{
	size_t          i;
	struct qm_move *m;

	if (mv == NULL)
		return;
	array_for_each(mv, i, m) {
		free(m->a1);
		free(m->a2);
		free(m->a3);
		free(m);
	}
	array_free(mv);
}

static array *
qm_parse_moves(const char *bufc)
{
	array *mv  = array_new();
	char  *tmp = xstrdup(bufc);
	char  *line;
	char  *lsp;

	for (line = strtok_r(tmp, "\r\n", &lsp);
		 line != NULL;
		 line = strtok_r(NULL, "\r\n", &lsp))
	{
		char *t1, *t2, *t3, *t4, *sp;

		if (line[0] == '#')
			continue;
		t1 = strtok_r(line, " \t", &sp);
		t2 = strtok_r(NULL, " \t", &sp);
		t3 = strtok_r(NULL, " \t", &sp);
		t4 = strtok_r(NULL, " \t", &sp);
		if (t1 == NULL)
			continue;
		if (strcmp(t1, "move") == 0 && t2 != NULL && t3 != NULL) {
			depend_atom *f = atom_explode(t2);
			depend_atom *g = atom_explode(t3);

			/* endpoints are bare cat/pn, never versioned */
			if (f == NULL || g == NULL ||
					f->CATEGORY == NULL || f->PN == NULL || f->PV != NULL ||
					g->CATEGORY == NULL || g->PN == NULL || g->PV != NULL) {
				warn("Moves: malformed move directive: %s %s",
					 t2 != NULL ? t2 : "?", t3 != NULL ? t3 : "?");
			} else {
				struct qm_move *m = xzalloc(sizeof(*m));

				xasprintf(&m->a1, "%s/%s", f->CATEGORY, f->PN);
				xasprintf(&m->a2, "%s/%s", g->CATEGORY, g->PN);
				array_append(mv, m);
			}
			if (f != NULL)
				atom_implode(f);
			if (g != NULL)
				atom_implode(g);
		} else if (strcmp(t1, "slotmove") == 0 &&
				   t2 != NULL && t3 != NULL && t4 != NULL) {
			struct qm_move *m = xzalloc(sizeof(*m));

			m->slotmove = true;
			m->a1 = xstrdup(t2);
			m->a2 = xstrdup(t3);
			m->a3 = xstrdup(t4);
			array_append(mv, m);
		} else {
			warn("Moves: unrecognised directive: %s", t1);
		}
	}
	free(tmp);
	return mv;
}

/* atom-aware cat/pn swap in a dependency/world string (portage
 * update_dbentry equivalent): the cat/pn segment starts after any
 * !<>=~ prefix and ends before -<ver>, :slot, [use], * or token end */
static bool
qm_move_rewrite_str(const char *in, const char *oldcp, const char *newcp,
					char **outp)
{
	size_t      olen = strlen(oldcp);
	size_t      nlen = strlen(newcp);
	size_t      occ  = 0;
	const char *p;
	char       *out;
	char       *o;
	bool        changed = false;

	for (p = in; (p = strstr(p, oldcp)) != NULL; p += olen)
		occ++;
	if (occ == 0)
		return false;
	out = xmalloc(strlen(in) + occ * (nlen > olen ? nlen - olen : 0) + 1);
	o = out;
	p = in;
	while (*p != '\0') {
		const char *tok;
		size_t      toklen;
		const char *m;

		while (*p != '\0' && isspace((unsigned char)*p))
			*o++ = *p++;
		if (*p == '\0')
			break;
		tok = p;
		while (*p != '\0' && !isspace((unsigned char)*p))
			p++;
		toklen = (size_t)(p - tok);

		m = tok;
		while (m < tok + toklen &&
				(*m == '!' || *m == '<' || *m == '>' ||
				 *m == '=' || *m == '~'))
			m++;
		if ((size_t)(tok + toklen - m) >= olen &&
				strncmp(m, oldcp, olen) == 0) {
			char c = (size_t)(m - tok) + olen < toklen ? m[olen] : '\0';

			if (c == '\0' || c == ':' || c == '[' || c == '*' ||
					(c == '-' && isdigit((unsigned char)m[olen + 1]))) {
				memcpy(o, tok, (size_t)(m - tok));
				o += m - tok;
				memcpy(o, newcp, nlen);
				o += nlen;
				memcpy(o, m + olen, toklen - (size_t)(m - tok) - olen);
				o += toklen - (size_t)(m - tok) - olen;
				changed = true;
				continue;
			}
		}
		memcpy(o, tok, toklen);
		o += toklen;
	}
	*o = '\0';
	if (!changed) {
		free(out);
		return false;
	}
	*outp = out;
	return true;
}

static bool
qm_move_rewrite_file(const char *path, const char *oldcp, const char *newcp)
{
	char  *buf = NULL;
	size_t len = 0;
	char  *nb  = NULL;
	FILE  *f;

	if (!eat_file(path, &buf, &len) || buf == NULL) {
		free(buf);
		return false;
	}
	if (!qm_move_rewrite_str(buf, oldcp, newcp, &nb)) {
		free(buf);
		return false;
	}
	f = fopen(path, "w");
	if (f != NULL) {
		fputs(nb, f);
		fclose(f);
	} else {
		warnp("Moves: cannot rewrite %s", path);
	}
	free(buf);
	free(nb);
	return true;
}

/* rename the VDB entries of oldcp to newcp (dir, CATEGORY, PF);
 * collision with an existing entry under the new name = skip + warn */
static int
qm_apply_move_ent(const char *oldcp, const char *newcp)
{
	char           oldcat[128];
	char           oldpn[128];
	char           newcat[128];
	char           newpn[128];
	char          *cdir;
	DIR           *d;
	struct dirent *de;
	int            moved = 0;
	const char    *s;

	s = strchr(oldcp, '/');
	snprintf(oldcat, sizeof(oldcat), "%.*s", (int)(s - oldcp), oldcp);
	snprintf(oldpn, sizeof(oldpn), "%s", s + 1);
	s = strchr(newcp, '/');
	snprintf(newcat, sizeof(newcat), "%.*s", (int)(s - newcp), newcp);
	snprintf(newpn, sizeof(newpn), "%s", s + 1);

	xasprintf(&cdir, "%s%s/%s", portroot, portvdb, oldcat);
	d = opendir(cdir);
	if (d == NULL) {
		free(cdir);
		return 0;
	}
	while ((de = readdir(d)) != NULL) {
		char         *cpvbuf;
		depend_atom  *a;
		char         *oldpath;
		char         *newcdir;
		char         *newpath;
		char         *fpath;
		FILE         *f;
		struct stat   st;
		bool          pnmatch;

		if (de->d_name[0] == '.' || de->d_name[0] == '-')
			continue;
		xasprintf(&cpvbuf, "%s/%s", oldcat, de->d_name);
		a = atom_explode(cpvbuf);
		pnmatch = a != NULL && a->PN != NULL && strcmp(a->PN, oldpn) == 0;
		if (a != NULL)
			atom_implode(a);
		free(cpvbuf);
		if (!pnmatch)
			continue;

		xasprintf(&oldpath, "%s/%s", cdir, de->d_name);
		xasprintf(&newcdir, "%s%s/%s", portroot, portvdb, newcat);
		xasprintf(&newpath, "%s/%s%s", newcdir, newpn,
				  de->d_name + strlen(oldpn));
		if (stat(newpath, &st) == 0) {
			warn("Moves: %s exists, not moving %s/%s (collision)",
				 newpath, oldcat, de->d_name);
		} else if (mkdir_p(newcdir, 0755) != 0 ||
				   rename(oldpath, newpath) != 0) {
			warnp("Moves: cannot move %s to %s", oldpath, newpath);
		} else {
			xasprintf(&fpath, "%s/CATEGORY", newpath);
			f = fopen(fpath, "w");
			if (f != NULL) {
				fprintf(f, "%s\n", newcat);
				fclose(f);
			}
			free(fpath);
			xasprintf(&fpath, "%s/PF", newpath);
			f = fopen(fpath, "w");
			if (f != NULL) {
				fprintf(f, "%s%s\n", newpn, de->d_name + strlen(oldpn));
				fclose(f);
			}
			free(fpath);
			qprintf("%s>>>%s package move: %s/%s -> %s/%s%s\n",
					GREEN, NORM, oldcat, de->d_name, newcat, newpn,
					de->d_name + strlen(oldpn));
			moved++;
		}
		free(oldpath);
		free(newcdir);
		free(newpath);
	}
	closedir(d);
	/* only succeeds when the old category dir emptied */
	rmdir(cdir);
	free(cdir);
	return moved;
}

static int
qm_apply_slotmove(const char *atomstr, const char *olds, const char *news)
{
	depend_atom  *qa = atom_explode(atomstr);
	tree_ctx     *vdb;
	array        *t;
	size_t        n;
	tree_pkg_ctx *p;
	int           hits = 0;

	if (qa == NULL) {
		warn("Moves: malformed slotmove atom: %s", atomstr);
		return 0;
	}
	vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);
	if (vdb == NULL) {
		atom_implode(qa);
		return 0;
	}
	t = tree_match_atom(vdb, qa, TREE_MATCH_SORT);
	array_for_each(t, n, p) {
		char        *slot = tree_pkg_meta(p, Q_SLOT);
		depend_atom *pa   = tree_pkg_atom(p, false);
		char        *spath;
		FILE        *f;

		if (slot == NULL || strcmp(slot, olds) != 0)
			continue;
		xasprintf(&spath, "%s%s/%s/%s/SLOT",
				  portroot, portvdb, pa->CATEGORY, pa->PF);
		f = fopen(spath, "w");
		if (f != NULL) {
			fprintf(f, "%s\n", news);
			fclose(f);
			qprintf("%s>>>%s slotmove: %s/%s :%s -> :%s\n",
					GREEN, NORM, pa->CATEGORY, pa->PF, olds, news);
			hits++;
		}
		free(spath);
	}
	array_free(t);
	tree_close(vdb);
	atom_implode(qa);
	return hits;
}

static const char * const qm_move_depfiles[] = {
	"RDEPEND", "DEPEND", "PDEPEND", "BDEPEND", "IDEPEND", NULL
};

/* rewrite old cat/pn references in every installed pkg's dep strings
 * (runs even when oldcp itself is not installed: consumers may still
 * reference the old name) */
static void
qm_move_vdb_deps(const char *oldcp, const char *newcp)
{
	char          *vdir;
	DIR           *cd;
	struct dirent *ce;

	xasprintf(&vdir, "%s%s", portroot, portvdb);
	cd = opendir(vdir);
	if (cd == NULL) {
		free(vdir);
		return;
	}
	while ((ce = readdir(cd)) != NULL) {
		char          *pdir;
		DIR           *pd;
		struct dirent *pe;

		if (ce->d_name[0] == '.' || ce->d_name[0] == '-')
			continue;
		xasprintf(&pdir, "%s/%s", vdir, ce->d_name);
		pd = opendir(pdir);
		if (pd == NULL) {
			free(pdir);
			continue;
		}
		while ((pe = readdir(pd)) != NULL) {
			size_t di;

			if (pe->d_name[0] == '.' || pe->d_name[0] == '-')
				continue;
			for (di = 0; qm_move_depfiles[di] != NULL; di++) {
				char *fp;

				xasprintf(&fp, "%s/%s/%s",
						  pdir, pe->d_name, qm_move_depfiles[di]);
				(void)qm_move_rewrite_file(fp, oldcp, newcp);
				free(fp);
			}
		}
		closedir(pd);
		free(pdir);
	}
	closedir(cd);
	free(vdir);
}

static void
qm_move_world(const char *oldcp, const char *newcp)
{
	char *wpath;

	xasprintf(&wpath, "%svar/lib/portage/world", portroot);
	if (qm_move_rewrite_file(wpath, oldcp, newcp))
		qprintf("%s>>>%s world: %s -> %s\n", GREEN, NORM, oldcp, newcp);
	free(wpath);
}

/* chronological concatenation of the main repo's profiles/updates
 * files; NULL when this host has no repo checkout */
struct qm_updfile {
	int   year;
	int   quarter;
	char *name;
};

static int
qm_updfile_cmp(const void *va, const void *vb)
{
	const struct qm_updfile *a = va;
	const struct qm_updfile *b = vb;

	if (a->year != b->year)
		return a->year - b->year;
	return a->quarter - b->quarter;
}

static char *
qm_collect_updates(void)
{
	char               updir[_Q_PATH_MAX];
	DIR               *d;
	struct dirent     *de;
	struct qm_updfile *list = NULL;
	size_t             cnt  = 0;
	size_t             cap  = 0;
	size_t             i;
	char              *out  = NULL;
	size_t             olen = 0;

	if (main_overlay == NULL)
		return NULL;
	snprintf(updir, sizeof(updir), "%s/profiles/updates", main_overlay);
	d = opendir(updir);
	if (d == NULL)
		return NULL;
	while ((de = readdir(d)) != NULL) {
		int q, y;

		if (sscanf(de->d_name, "%dQ-%d", &q, &y) != 2)
			continue;
		if (cnt == cap) {
			cap  = cap > 0 ? cap * 2 : 16;
			list = xrealloc(list, cap * sizeof(*list));
		}
		list[cnt].year    = y;
		list[cnt].quarter = q;
		list[cnt].name    = xstrdup(de->d_name);
		cnt++;
	}
	closedir(d);
	if (cnt == 0) {
		free(list);
		return NULL;
	}
	qsort(list, cnt, sizeof(*list), qm_updfile_cmp);
	for (i = 0; i < cnt; i++) {
		char  *fp   = NULL;
		char  *fbuf = NULL;
		size_t flen = 0;

		xasprintf(&fp, "%s/%s", updir, list[i].name);
		/* eat_file's len is buffer capacity, use the string length */
		if (eat_file(fp, &fbuf, &flen) && fbuf != NULL && fbuf[0] != '\0') {
			size_t clen = strlen(fbuf);

			out = xrealloc(out, olen + clen + 2);
			memcpy(out + olen, fbuf, clen);
			olen += clen;
			if (out[olen - 1] != '\n')
				out[olen++] = '\n';
			out[olen] = '\0';
		}
		free(fp);
		free(fbuf);
		free(list[i].name);
	}
	free(list);
	return out;
}

/* does any binhost catalog carry cp at all */
static bool
qm_bin_has_cp(const char *cp)
{
	depend_atom *a = atom_explode(cp);
	size_t       ri;
	size_t       rcnt  = qm_bintree_cnt();
	bool         found = false;

	if (a == NULL)
		return false;
	for (ri = 0; ri < rcnt && !found; ri++) {
		tree_ctx *t = qm_bintree(ri);
		array    *m;

		if (t == NULL)
			continue;
		m = tree_match_atom(t, a,
				TREE_MATCH_SORT | TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);
		if (m != NULL && array_cnt(m) > 0)
			found = true;
		array_free(m);
	}
	atom_implode(a);
	return found;
}

/* apply one directive stream; content snapshot in apath makes it
 * one-shot.  trusted = local repo data, exempt from the signature
 * posture that gates the fetched transport.  Returns -1 when skipped
 * (unchanged/refused), else the number of VDB mutations. */
static int
qm_apply_moves_buf(const char *mbuf, const char *rname, const char *apath,
				   bool trusted)
{
	char           *abuf = NULL;
	size_t          alen = 0;
	array          *mv;
	size_t          mi;
	struct qm_move *m;
	int             applied = 0;

	if (mbuf == NULL || mbuf[0] == '\0')
		return -1;
	if (eat_file(apath, &abuf, &alen) && abuf != NULL &&
			strcmp(abuf, mbuf) == 0) {
		free(abuf);
		return -1;
	}
	free(abuf);
	/* VDB rewriting is security-sensitive: under a mandatory signature
	 * posture an unsigned fetched Moves is refused (signed Moves
	 * support lands with binhost signing) */
	if (!trusted && contains_set("binpkg-request-signature", features)) {
		warn("Moves from %s is unsigned but FEATURES="
			 "binpkg-request-signature is set -- not applying", rname);
		return -1;
	}
	mv = qm_parse_moves(mbuf);
	array_for_each(mv, mi, m) {
		if (m->slotmove) {
			applied += qm_apply_slotmove(m->a1, m->a2, m->a3);
		} else {
			int mvd = qm_apply_move_ent(m->a1, m->a2);

			applied += mvd;
			qm_move_vdb_deps(m->a1, m->a2);
			qm_move_world(m->a1, m->a2);
			/* the source tree renamed an INSTALLED pkg but no binhost
			 * carries the new name yet: tell the user instead of
			 * letting the next resolve fail bare */
			if (mvd > 0 && !qm_bin_has_cp(m->a2))
				warn("source tree moved %s to %s but no prebuilt "
					 "binary of %s exists on any binhost yet; "
					 "use emerge to compile it", m->a1, m->a2, m->a2);
		}
	}
	qm_moves_free(mv);
	if (applied > 0)
		qprintf("%s>>>%s applied %d package move(s) from %s\n",
				GREEN, NORM, applied, rname);
	{
		FILE *f = fopen(apath, "w");

		if (f != NULL) {
			fputs(mbuf, f);
			fclose(f);
		}
	}
	return applied;
}

/* apply every store's fetched Moves; true when any store had one */
static bool
qm_apply_moves_binhost(void)
{
	size_t nrepo = qm_nbinrepos > 0 ? qm_nbinrepos : 1;
	size_t i;
	bool   any   = false;

	for (i = 0; i < nrepo; i++) {
		char        locbuf[_Q_PATH_MAX];
		const char *loc = qm_nbinrepos > 0 ?
				qm_repo_loc(i, locbuf, sizeof(locbuf)) : pkgdir;
		const char *rname = qm_nbinrepos > 0 ?
				qm_binrepos[i].name : "binhost";
		char       *mpath = NULL;
		char       *apath = NULL;
		char       *mbuf  = NULL;
		size_t      mlen  = 0;

		xasprintf(&mpath, "%s%s/Moves", portroot, loc);
		xasprintf(&apath, "%s%s/.moves-applied", portroot, loc);
		if (eat_file(mpath, &mbuf, &mlen) &&
				mbuf != NULL && mbuf[0] != '\0') {
			any = true;
			(void)qm_apply_moves_buf(mbuf, rname, apath, false);
		}
		free(mpath);
		free(apath);
		free(mbuf);
	}
	return any;
}

/* apply the repo's own profiles/updates; the source of truth portage
 * applies on sync.  notice = mention outranked binhost Moves files */
static void
qm_apply_moves_repo(const char *repoupd, bool notice)
{
	char  *edir;
	char  *apath;
	bool   have_moves = false;
	size_t nrepo = qm_nbinrepos > 0 ? qm_nbinrepos : 1;
	size_t i;

	if (repoupd == NULL)
		return;
	if (notice) {
		for (i = 0; i < nrepo && !have_moves; i++) {
			char        locbuf[_Q_PATH_MAX];
			const char *loc = qm_nbinrepos > 0 ?
					qm_repo_loc(i, locbuf, sizeof(locbuf)) : pkgdir;
			char       *mp;
			struct stat st;

			xasprintf(&mp, "%s%s/Moves", portroot, loc);
			have_moves = stat(mp, &st) == 0 && st.st_size > 0;
			free(mp);
		}
	}
	xasprintf(&edir, "%s%s", portroot, portedb);
	mkdir_p(edir, 0755);
	xasprintf(&apath, "%s/.qmerge-moves-applied", edir);
	if (qm_apply_moves_buf(repoupd, "repo profiles/updates",
						   apath, true) >= 0 && have_moves)
		qprintf("%s>>>%s repo profiles/updates take priority; "
				"binhost Moves files ignored\n", GREEN, NORM);
	free(apath);
	free(edir);
}

static void
qm_apply_moves_all(void)
{
	enum qm_mvpol pol = qm_moves_policy();
	char         *repoupd;

	if (pol == QM_MV_NONE)
		return;

	if (pol == QM_MV_BINHOST || pol == QM_MV_BINHOST_ONLY) {
		if (!qm_apply_moves_binhost() && pol == QM_MV_BINHOST) {
			repoupd = qm_collect_updates();
			qm_apply_moves_repo(repoupd, false);
			free(repoupd);
		}
		return;
	}

	repoupd = qm_collect_updates();
	if (repoupd != NULL)
		qm_apply_moves_repo(repoupd, pol == QM_MV_REPO);
	else if (pol == QM_MV_REPO)
		(void)qm_apply_moves_binhost();
	free(repoupd);
}

/* move-directive map for resolve-time diagnostics: repo updates when
 * present, else the fetched Moves files */
static array *qm_moves_map        = NULL;
static bool   qm_moves_map_loaded = false;

/* concatenation of every store's fetched Moves content */
static char *
qm_collect_store_moves(void)
{
	char  *buf   = NULL;
	size_t olen  = 0;
	size_t nrepo = qm_nbinrepos > 0 ? qm_nbinrepos : 1;
	size_t i;

	for (i = 0; i < nrepo; i++) {
		char        locbuf[_Q_PATH_MAX];
		const char *loc = qm_nbinrepos > 0 ?
				qm_repo_loc(i, locbuf, sizeof(locbuf)) : pkgdir;
		char       *mp;
		char       *mbuf = NULL;
		size_t      mlen = 0;

		xasprintf(&mp, "%s%s/Moves", portroot, loc);
		/* eat_file's len is buffer capacity, use the string length */
		if (eat_file(mp, &mbuf, &mlen) && mbuf != NULL &&
				mbuf[0] != '\0') {
			size_t clen = strlen(mbuf);

			buf = xrealloc(buf, olen + clen + 2);
			memcpy(buf + olen, mbuf, clen);
			olen += clen;
			if (buf[olen - 1] != '\n')
				buf[olen++] = '\n';
			buf[olen] = '\0';
		}
		free(mp);
		free(mbuf);
	}
	return buf;
}

static void
qm_moves_map_load(void)
{
	enum qm_mvpol pol = qm_moves_policy();
	char         *buf = NULL;

	if (qm_moves_map_loaded)
		return;
	qm_moves_map_loaded = true;
	if (pol == QM_MV_NONE)
		return;
	/* mirror the apply policy so hints never cite a disabled source */
	if (pol == QM_MV_BINHOST || pol == QM_MV_BINHOST_ONLY) {
		buf = qm_collect_store_moves();
		if (buf == NULL && pol == QM_MV_BINHOST)
			buf = qm_collect_updates();
	} else {
		buf = qm_collect_updates();
		if (buf == NULL && pol == QM_MV_REPO)
			buf = qm_collect_store_moves();
	}
	if (buf != NULL) {
		qm_moves_map = qm_parse_moves(buf);
		free(buf);
	}
}

/* cannot-satisfy diagnostic: the atom is an endpoint of a known move */
static const char *
qm_move_fail_hint(const depend_atom *atom)
{
	static char     hint[320];
	size_t          i;
	struct qm_move *m;
	char            cp[256];

	if (atom == NULL || atom->CATEGORY == NULL || atom->PN == NULL)
		return "";
	qm_moves_map_load();
	if (qm_moves_map == NULL)
		return "";
	snprintf(cp, sizeof(cp), "%s/%s", atom->CATEGORY, atom->PN);
	array_for_each(qm_moves_map, i, m) {
		if (m->slotmove)
			continue;
		if (strcmp(cp, m->a2) == 0) {
			snprintf(hint, sizeof(hint),
					 " (moved from %s in the source tree; no binpkg "
					 "built yet; try emerge to compile it)",
					 m->a1);
			return hint;
		}
		if (strcmp(cp, m->a1) == 0) {
			snprintf(hint, sizeof(hint),
					 " (moved to %s in the source tree; try that name)",
					 m->a2);
			return hint;
		}
	}
	return "";
}

/* GLEP 42 news transport: the binhost publishes the repo's
 * metadata/news as <PKGDIR>/News.tar (members <repoid>/<item>/<file>),
 * the repo-less client fetches it with the index, filters relevance
 * and does the unread/skip bookkeeping; bodies for relevant items are
 * cached under /var/lib/gentoo/news/items/<repoid>/<item>/ where the
 * qnews applet reads them */
static void
qm_emit_news(const char *pdir)
{
	char           ndir[_Q_PATH_MAX];
	char           rnp[_Q_PATH_MAX];
	char          *repoid = NULL;
	size_t         rlen   = 0;
	DIR           *d;
	struct dirent *de;
	struct archive *aw    = NULL;
	char           npath[_Q_PATH_MAX + 16];
	int            items  = 0;

	if (!qnews_enable || main_overlay == NULL)
		return;
	snprintf(ndir, sizeof(ndir), "%s/metadata/news", main_overlay);
	d = opendir(ndir);
	if (d == NULL)
		return;
	snprintf(rnp, sizeof(rnp), "%s/profiles/repo_name", main_overlay);
	if (!eat_file(rnp, &repoid, &rlen) || repoid == NULL ||
			repoid[0] == '\0') {
		free(repoid);
		closedir(d);
		return;
	}
	rmspace(repoid);

	snprintf(npath, sizeof(npath), "%s/News.tar", pdir);
	while ((de = readdir(d)) != NULL) {
		char          *idir;
		DIR           *id;
		struct dirent *fe;

		if (de->d_name[0] == '.')
			continue;
		xasprintf(&idir, "%s/%s", ndir, de->d_name);
		id = opendir(idir);
		if (id == NULL) {
			free(idir);
			continue;
		}
		while ((fe = readdir(id)) != NULL) {
			char       *fpath;
			char        ename[_Q_PATH_MAX];
			char       *fbuf = NULL;
			size_t      flen = 0;
			size_t      clen;
			struct archive_entry *e;

			if (fe->d_name[0] == '.')
				continue;
			xasprintf(&fpath, "%s/%s", idir, fe->d_name);
			if (!eat_file(fpath, &fbuf, &flen) || fbuf == NULL) {
				free(fbuf);
				free(fpath);
				continue;
			}
			if (aw == NULL) {
				aw = archive_write_new();
				archive_write_set_format_ustar(aw);
				if (archive_write_open_filename(aw, npath) != ARCHIVE_OK) {
					warn("cannot write %s", npath);
					archive_write_free(aw);
					aw = NULL;
					free(fbuf);
					free(fpath);
					break;
				}
			}
			clen = strlen(fbuf);
			snprintf(ename, sizeof(ename), "%s/%s/%s",
					 repoid, de->d_name, fe->d_name);
			e = archive_entry_new();
			archive_entry_set_pathname(e, ename);
			archive_entry_set_size(e, (la_int64_t)clen);
			archive_entry_set_filetype(e, AE_IFREG);
			archive_entry_set_perm(e, 0644);
			archive_write_header(aw, e);
			archive_write_data(aw, fbuf, clen);
			archive_entry_free(e);
			free(fbuf);
			free(fpath);
		}
		closedir(id);
		free(idir);
		items++;
	}
	closedir(d);
	if (aw != NULL) {
		archive_write_close(aw);
		archive_write_free(aw);
		binpkg_perms(npath, false);
		qprintf("%s>>>%s wrote %s (%d news item%s)\n",
				GREEN, NORM, npath, items, items == 1 ? "" : "s");
	}
	free(repoid);
}

/* GLEP 42 relevance: OR within a Display-If type, AND across types;
 * absent type = no constraint; no headers at all = relevant */
static bool
qm_news_relevant(const char *hdrs)
{
	char *tmp = xstrdup(hdrs);
	char *line;
	char *lsp;
	bool  have_inst = false, ok_inst = false;
	bool  have_kw   = false, ok_kw   = false;
	bool  have_prof = false, ok_prof = false;
	static char prof[_Q_PATH_MAX];
	static bool prof_init = false;

	if (!prof_init) {
		char  lp[_Q_PATH_MAX];
		char  rp[_Q_PATH_MAX];
		char *sub;

		prof_init = true;
		prof[0] = '\0';
		snprintf(lp, sizeof(lp), "%setc/portage/make.profile", portroot);
		if (realpath(lp, rp) != NULL &&
				(sub = strstr(rp, "/profiles/")) != NULL)
			snprintf(prof, sizeof(prof), "%s",
					 sub + sizeof("/profiles/") - 1);
	}

	for (line = strtok_r(tmp, "\r\n", &lsp);
		 line != NULL;
		 line = strtok_r(NULL, "\r\n", &lsp))
	{
		char *v;

		if (line[0] == '\0')
			break;
		v = strchr(line, ':');
		if (v == NULL)
			continue;
		*v++ = '\0';
		v = rmspace(v);
		if (strcmp(line, "Display-If-Installed") == 0) {
			depend_atom *qa;

			have_inst = true;
			if (ok_inst)
				continue;
			qa = atom_explode(v);
			if (qa != NULL) {
				tree_ctx *vdb = tree_new(portroot, portvdb,
										 TREETYPE_VDB, true);

				if (vdb != NULL) {
					array *m = tree_match_atom(vdb, qa, TREE_MATCH_SORT);

					if (m != NULL && array_cnt(m) > 0)
						ok_inst = true;
					array_free(m);
					tree_close(vdb);
				}
				atom_implode(qa);
			}
		} else if (strcmp(line, "Display-If-Keyword") == 0) {
			/* no derivable arch = keyword-scoped items never match */
			const char *earch = qm_effective_arch();

			have_kw = true;
			if (earch != NULL && earch[0] != '\0' &&
					strcmp(v, earch) == 0)
				ok_kw = true;
		} else if (strcmp(line, "Display-If-Profile") == 0) {
			size_t vl = strlen(v);

			have_prof = true;
			if (prof[0] == '\0')
				continue;
			if (vl > 1 && v[vl - 1] == '*' && v[vl - 2] == '/') {
				if (strncmp(prof, v, vl - 1) == 0)
					ok_prof = true;
			} else if (strcmp(prof, v) == 0) {
				ok_prof = true;
			}
		}
	}
	free(tmp);
	if (have_inst && !ok_inst)
		return false;
	if (have_kw && !ok_kw)
		return false;
	if (have_prof && !ok_prof)
		return false;
	return true;
}

static bool
qm_news_id_seen(const char *ndir, const char *repoid, const char *nid)
{
	static const char * const sufs[] = { "unread", "read", "skip", NULL };
	size_t i;
	bool   seen = false;

	for (i = 0; sufs[i] != NULL && !seen; i++) {
		char   p[_Q_PATH_MAX + 256];
		char  *buf = NULL;
		size_t len = 0;
		char  *line;
		char  *sp;

		snprintf(p, sizeof(p), "%s/news-%s.%s", ndir, repoid, sufs[i]);
		if (!eat_file(p, &buf, &len) || buf == NULL) {
			free(buf);
			continue;
		}
		for (line = strtok_r(buf, "\r\n", &sp);
			 line != NULL && !seen;
			 line = strtok_r(NULL, "\r\n", &sp))
			if (strcmp(line, nid) == 0)
				seen = true;
		free(buf);
	}
	return seen;
}

static void
qm_news_mark_unread(const char *ndir, const char *repoid, const char *nid)
{
	static const char * const sufs[] = { "unread", "skip", NULL };
	size_t i;

	for (i = 0; sufs[i] != NULL; i++) {
		char  p[_Q_PATH_MAX + 256];
		FILE *f;

		snprintf(p, sizeof(p), "%s/news-%s.%s", ndir, repoid, sufs[i]);
		f = fopen(p, "a");
		if (f != NULL) {
			fprintf(f, "%s\n", nid);
			fclose(f);
			chmod(p, 0644);
		}
	}
}

/* filter one store's fetched News.tar and cache relevant item bodies;
 * one-shot per content via an md5 marker next to it */
static void
qm_apply_news_one(const char *loc, const char *rname)
{
	char            tpath[_Q_PATH_MAX + 16];
	char            mpath[_Q_PATH_MAX + 32];
	char           *mbuf = NULL;
	size_t          mlen = 0;
	char           *md5;
	char            md5s[34];
	struct archive *ar;
	struct archive_entry *e;
	set            *relevant = NULL;
	char            ndir[_Q_PATH_MAX];
	int             fresh = 0;

	snprintf(tpath, sizeof(tpath), "%s%s/News.tar", portroot, loc);
	if (access(tpath, R_OK) != 0)
		return;
	md5 = hash_file(tpath, HASH_MD5);
	if (md5 == NULL)
		return;
	snprintf(md5s, sizeof(md5s), "%s", md5);
	snprintf(mpath, sizeof(mpath), "%s%s/.news-applied", portroot, loc);
	if (eat_file(mpath, &mbuf, &mlen) && mbuf != NULL &&
			strcmp(rmspace(mbuf), md5s) == 0) {
		free(mbuf);
		return;
	}
	free(mbuf);
	if (contains_set("binpkg-request-signature", features)) {
		warn("News from %s is unsigned but FEATURES="
			 "binpkg-request-signature is set -- not applying", rname);
		return;
	}

	/* pass 1: relevance from each item's <id>.en.txt headers */
	ar = archive_read_new();
	archive_read_support_format_tar(ar);
	archive_read_support_filter_all(ar);
	if (archive_read_open_filename(ar, tpath, 65536) != ARCHIVE_OK) {
		archive_read_free(ar);
		return;
	}
	relevant = create_set();
	while (archive_read_next_header(ar, &e) == ARCHIVE_OK) {
		const char *nm = archive_entry_pathname(e);
		char        key[512];
		char        want[300];
		const char *p1, *p2;
		la_int64_t  sz;
		char       *body;

		if (nm == NULL || archive_entry_filetype(e) != AE_IFREG ||
				strstr(nm, "..") != NULL || nm[0] == '/')
			continue;
		p1 = strchr(nm, '/');
		p2 = p1 != NULL ? strchr(p1 + 1, '/') : NULL;
		if (p1 == NULL || p2 == NULL)
			continue;
		snprintf(want, sizeof(want), "%.*s.en.txt",
				 (int)(p2 - p1 - 1), p1 + 1);
		if (strcmp(p2 + 1, want) != 0)
			continue;
		sz = archive_entry_size(e);
		if (sz <= 0 || sz > 1024 * 1024)
			continue;
		body = xmalloc((size_t)sz + 1);
		if (archive_read_data(ar, body, (size_t)sz) != (la_ssize_t)sz) {
			free(body);
			continue;
		}
		body[sz] = '\0';
		if (qm_news_relevant(body)) {
			snprintf(key, sizeof(key), "%.*s", (int)(p2 - nm), nm);
			add_set(key, relevant);
		}
		free(body);
	}
	archive_read_free(ar);

	/* pass 2: cache bodies + unread/skip bookkeeping */
	snprintf(ndir, sizeof(ndir), "%svar/lib/gentoo/news", portroot);
	mkdir_p(ndir, 0755);
	ar = archive_read_new();
	archive_read_support_format_tar(ar);
	archive_read_support_filter_all(ar);
	if (archive_read_open_filename(ar, tpath, 65536) == ARCHIVE_OK) {
		while (archive_read_next_header(ar, &e) == ARCHIVE_OK) {
			const char *nm = archive_entry_pathname(e);
			char        key[512];
			char        repoid[128];
			char        nid[256];
			char        opath[_Q_PATH_MAX + 512];
			const char *p1, *p2;
			la_int64_t  sz;
			char       *body;
			FILE       *f;

			if (nm == NULL || archive_entry_filetype(e) != AE_IFREG ||
					strstr(nm, "..") != NULL || nm[0] == '/')
				continue;
			p1 = strchr(nm, '/');
			p2 = p1 != NULL ? strchr(p1 + 1, '/') : NULL;
			if (p1 == NULL || p2 == NULL)
				continue;
			snprintf(key, sizeof(key), "%.*s", (int)(p2 - nm), nm);
			if (contains_set(key, relevant) == NULL)
				continue;
			snprintf(repoid, sizeof(repoid), "%.*s",
					 (int)(p1 - nm), nm);
			snprintf(nid, sizeof(nid), "%.*s",
					 (int)(p2 - p1 - 1), p1 + 1);
			sz = archive_entry_size(e);
			if (sz < 0 || sz > 1024 * 1024)
				continue;
			body = xmalloc((size_t)sz + 1);
			if (archive_read_data(ar, body, (size_t)sz) !=
					(la_ssize_t)sz) {
				free(body);
				continue;
			}
			snprintf(opath, sizeof(opath), "%s/items/%s/%s",
					 ndir, repoid, nid);
			mkdir_p(opath, 0755);
			snprintf(opath, sizeof(opath), "%s/items/%s/%s/%s",
					 ndir, repoid, nid, p2 + 1);
			f = fopen(opath, "w");
			if (f != NULL) {
				fwrite(body, 1, (size_t)sz, f);
				fclose(f);
				chmod(opath, 0644);
			}
			free(body);
			if (!qm_news_id_seen(ndir, repoid, nid)) {
				qm_news_mark_unread(ndir, repoid, nid);
				fresh++;
			}
		}
		archive_read_free(ar);
	}
	free_set(relevant);
	if (fresh > 0)
		qprintf("%s>>>%s %d new news item%s from %s\n",
				GREEN, NORM, fresh, fresh == 1 ? "" : "s", rname);
	{
		FILE *f = fopen(mpath, "w");

		if (f != NULL) {
			fprintf(f, "%s\n", md5s);
			fclose(f);
		}
	}
}

static void
qm_apply_news_all(void)
{
	size_t nrepo = qm_nbinrepos > 0 ? qm_nbinrepos : 1;
	size_t i;

	if (!qnews_enable)
		return;

	for (i = 0; i < nrepo; i++) {
		char        locbuf[_Q_PATH_MAX];
		const char *loc = qm_nbinrepos > 0 ?
				qm_repo_loc(i, locbuf, sizeof(locbuf)) : pkgdir;
		const char *rname = qm_nbinrepos > 0 ?
				qm_binrepos[i].name : "binhost";

		qm_apply_news_one(loc, rname);
	}
}

/* server side: publish the main repo's move directives as
 * <PKGDIR>/Moves next to Packages for repo-less consumers */
static void
qm_emit_moves(const char *pdir)
{
	char  mpath[_Q_PATH_MAX + 8];
	char *content = qm_collect_updates();
	FILE *out;

	if (content == NULL)
		return;
	snprintf(mpath, sizeof(mpath), "%s/Moves", pdir);
	out = fopen(mpath, "w");
	if (out == NULL) {
		warnp("cannot write %s", mpath);
	} else {
		fputs(content, out);
		fclose(out);
		binpkg_perms(mpath, false);
		qprintf("%s>>>%s wrote %s (%zu bytes)\n",
				GREEN, NORM, mpath, strlen(content));
	}
	free(content);
}

static set *qm_flags_to_set(const char *str);

/* USE-gate rejections collected during resolution, printed as a
 * portage-style "ignored due to non matching USE" block with the plan */
static set *qm_use_rejects = NULL;

/* binpkg-respect-use, adapted for a config without ebuilds: verify a
 * (foreign-repo) binpkg's built USE against the local configuration.
 * We only check flags we have a strong signal for, explicit USE from
 * make.conf/package.use wildcards (must be on), profile use.force
 * (must be on) and use.mask (must be off), profile make.defaults USE
 * is not folded into ev_use, so full equality would falsely reject
 * nearly everything; this direction only produces true mismatches. */
static bool
binpkg_use_ok_r(tree_pkg_ctx *pkg, atom_ctx *patom, const char *rname,
				char *why, size_t whylen)
{
	char *iusestr = tree_pkg_meta(pkg, Q_IUSE);
	set  *built;
	char *tmp;
	char *tok;
	char *sp;
	bool  ok = true;

	if (iusestr == NULL || *iusestr == '\0')
		return true;

	built = qm_flags_to_set(tree_pkg_meta(pkg, Q_USE));
	tmp   = xstrdup(iusestr);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		bool have;
		char msg[512];

		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok == '\0')
			continue;

		have = contains_set(tok, built) != NULL;

		if (use_mask != NULL && contains_set(tok, use_mask) != NULL) {
			if (have) {
				if (why != NULL) {
					snprintf(why, whylen,
							 "built with %s (use.mask disables it)", tok);
				} else {
					snprintf(msg, sizeof(msg),
							 "=%s [%s] built with %s (use.mask disables it)",
							 atom_to_string(patom),
							 rname != NULL ? rname : "?", tok);
					qm_use_rejects =
							add_set_unique(msg, qm_use_rejects, NULL);
				}
				ok = false;
				break;
			}
			continue;
		}
		if ((use_force != NULL && contains_set(tok, use_force) != NULL) ||
				(ev_use != NULL && contains_set(tok, ev_use) != NULL))
		{
			if (!have) {
				if (why != NULL) {
					snprintf(why, whylen,
							 "built without %s (config wants %s)", tok, tok);
				} else {
					snprintf(msg, sizeof(msg),
							 "=%s [%s] built without %s (config wants %s)",
							 atom_to_string(patom),
							 rname != NULL ? rname : "?", tok, tok);
					qm_use_rejects =
							add_set_unique(msg, qm_use_rejects, NULL);
				}
				ok = false;
				break;
			}
		}
	}
	free(tmp);
	free_set(built);
	return ok;
}
#define binpkg_use_ok(P,A,R) binpkg_use_ok_r(P, A, R, NULL, 0)

/* USE difference of a (foreign) binpkg vs the installed version of the
 * same package, over the binpkg's IUSE; returns malloc'd "+a -b" or
 * NULL when identical */
static char *
qm_use_drift(tree_pkg_ctx *bpkg, tree_pkg_ctx *ipkg)
{
	char  *iusestr = tree_pkg_meta(bpkg, Q_IUSE);
	set   *bu;
	set   *iu;
	set   *oldiuse;
	char  *tmp;
	char  *tok;
	char  *sp;
	char   out[2048] = "";
	size_t olen = 0;

	if (iusestr == NULL || *iusestr == '\0')
		return NULL;

	bu      = qm_flags_to_set(tree_pkg_meta(bpkg, Q_USE));
	iu      = qm_flags_to_set(tree_pkg_meta(ipkg, Q_USE));
	oldiuse = qm_flags_to_set(tree_pkg_meta(ipkg, Q_IUSE));
	tmp = xstrdup(iusestr);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		bool b;
		bool iv;
		bool known;

		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok == '\0')
			continue;

		b  = contains_set(tok, bu) != NULL;
		iv = contains_set(tok, iu) != NULL;
		if (b == iv)
			continue;
		known = contains_set(tok, oldiuse) != NULL;
		if (olen + strlen(tok) + 24 >= sizeof(out))
			break;
		/* emerge colour semantics (output_helpers._create_use_string):
		 * a TOGGLED flag is green with a "*" marker; a flag the
		 * installed copy did not even know (new in IUSE) is yellow
		 * with "%".  Red/blue mean unchanged and never apply here. */
		olen += (size_t)snprintf(out + olen, sizeof(out) - olen,
								 "%s%s%c%s%s%s", olen > 0 ? " " : "",
								 *NORM == '\0' ? "" :
								 known ? "\033[32;01m" : "\033[33;01m",
								 b ? '+' : '-', tok, NORM,
								 known ? "*" : b ? "%*" : "%");
	}
	free(tmp);
	free_set(bu);
	free_set(iu);
	free_set(oldiuse);

	return olen > 0 ? xstrdup(out) : NULL;
}

/* plan-time notices for explicit binhost selections and affinity
 * pulls, grouped per package: full descriptive atom line -> set of
 * detail facts printed indented beneath it */
static hash_t *qm_plan_notices = NULL;

static void
qm_notice(const char *key, const char *detail)
{
	set *d;

	if (qm_plan_notices == NULL)
		qm_plan_notices = hash_new();
	d = hash_get(qm_plan_notices, key);
	if (d == NULL) {
		d = create_set();
		hash_add(qm_plan_notices, key, d, NULL);
	}
	add_set_unique(detail, d, NULL);
}

/* did the binpkg's built USE (over its IUSE) change vs the installed
 * copy?  PYTHON_TARGETS/RUBY_TARGETS/... are plain USE flags here, so a
 * remote rebuild with different targets registers as changed */
/* was the binpkg rebuilt after the installed copy was built?  Same
 * version, identical USE, newer BUILD_TIME, emerge --rebuilt-binaries
 * detection (e.g. remote rebuilds against a new toolchain) */
static bool
qm_rebuilt_newer(tree_pkg_ctx *bin, tree_pkg_ctx *inst)
{
	char               *bt;
	char               *it;
	unsigned long long  b;
	unsigned long long  iv;

	if (bin == NULL || inst == NULL)
		return false;
	bt = tree_pkg_meta(bin, Q_BUILD_TIME);
	it = tree_pkg_meta(inst, Q_BUILD_TIME);
	if (bt == NULL || *bt == '\0' || it == NULL || *it == '\0')
		return false;
	b  = strtoull(bt, NULL, 10);
	iv = strtoull(it, NULL, 10);
	/* --rebuilt-binaries-timestamp: ignore rebuilds older than the floor */
	if (qm_rebuilt_ts > 0 && b < qm_rebuilt_ts)
		return false;
	return b > iv;
}

static bool
qm_use_changed(tree_pkg_ctx *bin, tree_pkg_ctx *inst)
{
	char *d;

	if (bin == NULL || inst == NULL)
		return false;
	d = qm_use_drift(bin, inst);
	if (d == NULL)
		return false;
	free(d);
	return true;
}

static void
qm_print_use_rejects(void)
{
	array  *keys;
	size_t  n;
	char   *msg;

	if (qm_use_rejects != NULL && cnt_set(qm_use_rejects) > 0) {
		printf("\n%s!!!%s The following binary packages were ignored due "
			   "to non matching USE:\n", RED, NORM);
		keys = set_keys(qm_use_rejects);
		array_for_each(keys, n, msg)
			printf("    %s\n", msg);
		array_free(keys);
		printf("\n");
	}

	if (qm_lic_rejects != NULL && cnt_set(qm_lic_rejects) > 0) {
		printf("\n%s!!!%s The following binary packages were ignored due "
			   "to ACCEPT_LICENSE:\n", RED, NORM);
		keys = set_keys(qm_lic_rejects);
		array_for_each(keys, n, msg)
			printf("    %s\n", msg);
		array_free(keys);
		printf("\n");
	}

	if (qm_plan_notices != NULL && hash_size(qm_plan_notices) > 0) {
		printf("\n%s***%s Explicit binhost selections:\n", YELLOW, NORM);
		keys = hash_keys(qm_plan_notices);
		array_for_each(keys, n, msg) {
			set   *d = hash_get(qm_plan_notices, msg);
			array *dk;
			size_t dn;
			char  *dmsg;

			printf("    %s\n", msg);
			if (d == NULL)
				continue;
			dk = set_keys(d);
			array_for_each(dk, dn, dmsg)
				printf("        %s\n", dmsg);
			array_free(dk);
		}
		array_free(keys);
		printf("\n");
	}
}

static bool qm_usedep_ok(const atom_usedep *ud, set *cuse, set *ciuse,
						 set *puse);

/* parent USE context for USE-dep ([foo?]) evaluation inside
 * best_version's repo walk; set (scoped) by the resolver around its
 * calls, NULL means no USE-dep filtering (non-resolver callers) */
static set *_qm_bv_parent_use = NULL;

/* dep subtree affinity: when >0, best_version prefers this binrepo
 * before priority order (deps of an explicit pkg@repo target form a
 * consistent island from that repo); set (scoped) by qm_resolve */
static ssize_t _qm_repo_affinity = -1;

/* scoped: force newest-across-repos candidate selection (the conflict
 * repairer needs the real newest rebuild, not the priority-first pick,
 * which on a stale higher-priority repo is the already-installed
 * version) */
static bool _qm_bv_newest = false;

/* do the candidate's built USE/IUSE satisfy the dep atom's USE-deps? */
static bool
qm_cand_usedeps_ok(const depend_atom *atom, tree_pkg_ctx *cand)
{
	set  *cuse;
	set  *ciuse;
	const atom_usedep *ud;
	bool  ok = true;

	if (atom->usedeps == NULL)
		return true;

	cuse  = qm_flags_to_set(tree_pkg_meta(cand, Q_USE));
	ciuse = qm_flags_to_set(tree_pkg_meta(cand, Q_IUSE));
	for (ud = atom->usedeps; ud != NULL; ud = ud->next)
		if (!qm_usedep_ok(ud, cuse, ciuse, _qm_bv_parent_use)) {
			ok = false;
			break;
		}
	free_set(cuse);
	free_set(ciuse);
	return ok;
}

static tree_pkg_ctx *
best_version(const depend_atom *atom, int mode)
{
	tree_ctx       *vdb    = _qmerge_vdb_tree;
	tree_pkg_ctx   *tmv    = NULL;
	tree_pkg_ctx   *tmp    = NULL;
	tree_pkg_ctx   *ret;
	int             r;

	if (mode & BV_EBUILD) {
		warn("installing from ebuild not yet supported");
		return NULL;
	}
	if (mode == 0) {
		warn("mode needs to be set");
		return NULL;
	}

	if (mode & BV_VDB) {
		array *t;
		if (vdb == NULL) {
			vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);
			if (vdb == NULL)
				return NULL;
			_qmerge_vdb_tree = vdb;
		}
		t = tree_match_atom(vdb, atom,
				TREE_MATCH_LATEST  | TREE_MATCH_FIRST |
				TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);
		if (array_cnt(t) > 0)
			tmv = array_get(t, 0);
		array_free(t);
	}

	if (mode & BV_BINPKG) {
		size_t             rcnt          = qm_bintree_cnt();
		size_t             ri;
		bool               prefer_newest = _qm_bv_newest ||
				getenv("QMERGE_PREFER_NEWEST") != NULL;
		tree_pkg_ctx      *best          = NULL;
		ssize_t            only          = -1;
		depend_atom        qa;
		const depend_atom *qq            = atom;

		/* the ::@name marker (from the pkg@binrepo CLI sigil, or a
		 * cpv::@name plan pin) is an explicit binhost selector:
		 * restrict the walk to that repo.  Stripped for tree matching.
		 * A plain ::repo keeps the classic ebuild-repo meaning, so the
		 * two axes cannot collide once from-source builds land. */
		if (atom->REPO != NULL && atom->REPO[0] == '@' &&
				qm_nbinrepos > 0)
		{
			size_t k;

			for (k = 0; k < qm_nbinrepos; k++)
				if (strcmp(qm_binrepos[k].name, atom->REPO + 1) == 0) {
					only = (ssize_t)k;
					qa      = *atom;
					qa.REPO = NULL;
					qq      = &qa;
					break;
				}
			if (only < 0) {
				warn("unknown binhost '%s' in selector (configured: "
					 "see binrepos.conf)", atom->REPO + 1);
				rcnt = 0;   /* no walk: nothing can satisfy this */
			}
		}

		/* walk the binrepos in priority order; within a repo pick the
		 * highest VISIBLE version (skip package.mask'd, ~testing-not-
		 * accepted, ACCEPT_LICENSE-rejected; foreign repos additionally
		 * pass the USE-match gate).  Default policy: repo priority
		 * beats version, the first repo that can satisfy the atom
		 * wins, later repos are only consulted when it cannot.
		 * QMERGE_PREFER_NEWEST=1 switches to portage-style newest-
		 * across-all-repos.  An explicit ::binrepo selector walks ONLY
		 * that repo; its USE gate demotes to a notice (user knows best)
		 * and overriding a higher-priority repo is noticed too.  Quiet:
		 * we don't warn per skipped candidate (the merge-time gate is
		 * loud). */
		{
			size_t order[64];
			size_t no = 0;
			size_t oi;
			size_t k;

			/* walk order: an explicit selector is that repo only; an
			 * active subtree affinity goes first, then priority order */
			if (only >= 0) {
				order[no++] = (size_t)only;
			} else {
				if (_qm_repo_affinity > 0 &&
						(size_t)_qm_repo_affinity < rcnt)
					order[no++] = (size_t)_qm_repo_affinity;
				for (k = 0; k < rcnt && no < 64; k++)
					if (_qm_repo_affinity <= 0 ||
							k != (size_t)_qm_repo_affinity)
						order[no++] = k;
			}

			for (oi = 0; oi < no; oi++) {
				tree_ctx     *btree;
				array        *t;
				size_t        n;
				tree_pkg_ctx *cand;
				tree_pkg_ctx *rbest = NULL;
				bool          lenient;

				ri    = order[oi];
				btree = qm_bintree(ri);
				if (btree == NULL)
					continue;

				/* the primary stays ungated (trusted); an explicitly
				 * selected or affinity-preferred foreign repo demotes a
				 * USE mismatch to a notice (the user chose this island);
				 * other foreign repos reject on mismatch */
				lenient = ri > 0 &&
						((only >= 0 && ri == (size_t)only) ||
						 (only < 0 && _qm_repo_affinity > 0 &&
						  ri == (size_t)_qm_repo_affinity));

				t = tree_match_atom(btree, qq,
						TREE_MATCH_SORT | TREE_MATCH_VIRTUAL |
						TREE_MATCH_ACCT);
				array_for_each(t, n, cand) {
					depend_atom *pa = tree_pkg_atom(cand, true);

					if (binpkg_masked(pa))
						continue;
					if (!binpkg_keywords_ok(cand, pa, true))
						continue;
					if (!binpkg_license_ok(cand, pa, true))
						continue;
					if (binpkg_excluded(cand, pa, true))
						continue;
					/* USE-deps ([ssl] etc.) filter per candidate so an
					 * unsatisfying repo falls through to the next one
					 * instead of dead-ending resolution */
					if (!qm_cand_usedeps_ok(atom, cand))
						continue;
					if (lenient) {
						/* accepted regardless; the factual notice is
						 * emitted at pull time by qm_resolve */
					} else if (qm_respect_use != 0 &&
							   (ri > 0 || qm_respect_use == 1) &&
							   !binpkg_use_ok(cand, pa,
								qm_nbinrepos > 0 ?
								qm_binrepos[ri].name : NULL)) {
						continue;
					}
					rbest = cand;   /* highest-first: first visible = best */
					break;
				}
				array_free(t);

				if (only >= 0) {
					best = rbest;
					break;
				}
				if (rbest == NULL)
					continue;
				if (!prefer_newest) {
					best = rbest;
					break;
				}
				if (best == NULL ||
						atom_compare(tree_pkg_atom(rbest, false),
									 tree_pkg_atom(best, false)) == NEWER)
					best = rbest;
			}
		}

		/* explicit pick from a lower-priority repo: notice when a
		 * higher-priority repo could also satisfy the atom */
		if (only > 0 && best != NULL) {
			size_t k;

			for (k = 0; k < (size_t)only; k++) {
				tree_ctx *ktree = qm_bintree(k);
				array    *t;
				size_t    n;
				tree_pkg_ctx *cand;
				bool      found = false;

				if (ktree == NULL)
					continue;
				t = tree_match_atom(ktree, qq,
						TREE_MATCH_SORT | TREE_MATCH_VIRTUAL |
						TREE_MATCH_ACCT);
				array_for_each(t, n, cand) {
					depend_atom *pa = tree_pkg_atom(cand, true);

					if (binpkg_masked(pa) ||
							!binpkg_keywords_ok(cand, pa, true) ||
							!binpkg_license_ok(cand, pa, true) ||
							binpkg_excluded(cand, pa, true))
						continue;
					found = true;
					break;
				}
				array_free(t);
				if (found) {
					char key[512];
					char msg[512];

					snprintf(key, sizeof(key), "=%s [%s]",
							 atom_to_string(tree_pkg_atom(best, true)),
							 qm_binrepos[only].name);
					snprintf(msg, sizeof(msg),
							 "taken from lower-priority binhost, "
							 "overriding [%s]", qm_binrepos[k].name);
					qm_notice(key, msg);
					break;
				}
			}
		}
		tmv = best;
	}

	if (tmv == NULL && tmp == NULL)
		ret = NULL;
	else if (tmv == NULL && tmp != NULL)
		ret = tmp;
	else if (tmv != NULL && tmp == NULL)
		ret = tmv;
	else {
		if ((r = atom_compare(tree_pkg_atom(tmv, false),
							  tree_pkg_atom(tmp, false))) == EQUAL ||
			r == OLDER)
			ret = tmp;
		else
			ret = tmv;
	}

	return ret;
}

static int
config_protected(const char *buf, int cp_argc, char **cp_argv,
                 int cpm_argc, char **cpm_argv)
{
	int i;

	/* Check CONFIG_PROTECT_MASK */
	for (i = 1; i < cpm_argc; ++i)
		if (strncmp(cpm_argv[i], buf, strlen(cpm_argv[i])) == 0)
			return 0;

	/* Check CONFIG_PROTECT */
	for (i = 1; i < cp_argc; ++i)
		if (strncmp(cp_argv[i], buf, strlen(cp_argv[i])) == 0)
			return 1;

	/* this would probably be bad */
	if (strcmp(CONFIG_EPREFIX "bin/sh", buf) == 0)
		return 1;

	return 0;
}

static void
crossmount_rm(const char *fname, const struct stat * const st,
		int fd, char *qpth)
{
	struct stat lst;

	if (fstatat(fd, fname, &lst, AT_SYMLINK_NOFOLLOW) == -1)
		return;
	if (lst.st_dev != st->st_dev) {
		warn("skipping crossmount install masking: %s", fname);
		return;
	}
	qprintf("%s<<<%s %s/%s (INSTALL_MASK)\n", YELLOW, NORM, qpth, fname);
	rm_rf_at(fd, fname);
}

enum inc_exc { INCLUDE = 1, EXCLUDE = 2 };

static void
install_mask_check_dir(
		char ***maskv,
		int maskc,
		const struct stat * const st,
		int fd,
		ssize_t level,
		enum inc_exc parent_mode,
		char *qpth)
{
	struct dirent **files;
	int cnt;
	int i;
	int j;
	enum inc_exc mode;
	enum inc_exc child_mode;
	struct stat s;
	char *npth = qpth + strlen(qpth);

	cnt = scandirat(fd, ".", &files, filter_self_parent, alphasort);
	for (j = 0; j < cnt; j++) {
		mode = child_mode = parent_mode;
		for (i = 0; i < maskc; i++) {
			if ((ssize_t)maskv[i][0] < 0) {
				/* relative matches need to be a "file", as the Portage
				 * implementation suggests, so that's easy for us here,
				 * since we can just match it against each component in
				 * the path */
				if ((ssize_t)maskv[i][0] < -1)
					continue;  /* this is unsupported, so skip it */
				/* this also works if maskv happens to be a glob */
				if (fnmatch(maskv[i][1], files[j]->d_name, FNM_PERIOD) != 0)
					continue;
				mode = child_mode = maskv[i][2] ? INCLUDE : EXCLUDE;
			} else if ((ssize_t)maskv[i][0] < level) {
				/* either this is a mask that didn't match, or it
				 * matched, but a negative match exists for a deeper
				 * level, parent_mode should reflect this */
				continue;
			} else {
				if (fnmatch(maskv[i][level], files[j]->d_name, FNM_PERIOD) != 0)
					continue;

				if ((ssize_t)maskv[i][0] == level)  /* full mask match */
					mode = child_mode =
						(ssize_t)maskv[i][level + 1] ? INCLUDE : EXCLUDE;
				else if (maskv[i][(ssize_t)maskv[i][0] + 1])
					/* partial include mask */
					mode = INCLUDE;
			}
		}

		DBG("%s/%s: %s/%s", qpth, files[j]->d_name,
				mode == EXCLUDE       ? "EXCLUDE" : "INCLUDE",
				child_mode == EXCLUDE ? "EXCLUDE" : "INCLUDE");
		if (mode == EXCLUDE) {
			crossmount_rm(files[j]->d_name, st, fd, qpth);
			continue;
		}

		if (fstatat(fd, files[j]->d_name, &s, AT_SYMLINK_NOFOLLOW) != 0)
			continue;
		if (S_ISDIR(s.st_mode)) {
			int subfd = openat(fd, files[j]->d_name, O_RDONLY);
			if (subfd < 0)
				continue;
			snprintf(npth, _Q_PATH_MAX - (npth - qpth), "/%.*s",
					(int)(_Q_PATH_MAX - (npth - qpth)), files[j]->d_name);
			install_mask_check_dir(maskv, maskc, st, subfd,
					level + 1, child_mode, qpth);
			close(subfd);
			*npth = '\0';
		}
	}
	scandir_free(files, cnt);
}

static void
install_mask_pwd(int iargc, char **iargv, const struct stat * const st, int fd)
{
	char *p;
	char *q;
	int i;
	size_t cnt;
	size_t maxdirs;
	char **masks;
	size_t masksc;
	char ***masksv;
	char qpth[_Q_PATH_MAX];

	/* we have to deal with "negative" masks, see
	 * https://archives.gentoo.org/gentoo-portage-dev/message/29e128a9f41122fa0420c1140f7b7f94
	 * which means we'll need to see what thing matches last
	 * (inclusion or exclusion) for *every* file :( */

   /*
	example package contents:
	/e/t1
    /u/b/t1
	/u/b/t2
	/u/l/lt1
	/u/s/d/t1
	/u/s/m/m1/t1
	/u/s/m/m5/t2

	masking rules:     array encoding:
	 /u/s              2 u s 0          relative=0 include=0
	-/u/s/m/m1         4 u s m m1 1     relative=0 include=1
	 e                -1 e 0            relative=1 include=0

	should result in:
	/u/b/t1
	/u/b/t2
	/u/l/lt1
	/u/s/m/m1/t1
	strategy:
	- for each dir level
	  - find if there is a match on that level in rules
	  - if the last match is the full mask
	    - if the mask is negated, do not remove entry
	    - else, remove entry
	  - if the last match is negated, partial and a full mask matched before
	    - do not remove entry
	practice:
	/e | matches "e" -> remove
	/u | matches partial last negated -> continue
	  /b | doesn't match -> leave subtree
	  /l | doesn't match -> leave subtree
	  /s | match, partial last negated match -> remember match, continue
	    /d | doesn't match -> remembered match, remove subtree
		/m | partial match negated -> continue
		  /m1 | match negated -> leave subtree
		  /m5 | doesn't match -> remembered match, remove subtree
	*/

	/* find the longest path so we can allocate a matrix */
	maxdirs = 0;
	for (i = 1; i < iargc; i++) {
		char lastc = '/';

		cnt = 1; /* we always have "something", right? */
		p = iargv[i];
		if (*p == '-')
			p++;
		for (; *p != '\0'; p++) {
			/* eliminate duplicate /-es, also ignore the leading / in
			 * the count */
			if (*p == '/' && *p != lastc)
				cnt++;
			lastc = *p;
		}
		if (cnt > maxdirs)
			maxdirs = cnt;
	}
	maxdirs += 2;  /* allocate plus relative and include elements */

	/* allocate and populate matrix */
	masksc = iargc - 1;
	masks  = xmalloc(sizeof(char *) * (maxdirs * masksc));
	masksv = xmalloc(sizeof(char **) * (masksc));
	for (i = 1; i < iargc; i++)
	{
		masksv[i - 1] = &masks[(i - 1) * maxdirs];
		p             = iargv[i];
		cnt           = 1;  /* first level is reserved for count */

		/* ignore include marker */
		if (*p == '-')
			p++;
		for (q = p; *p != '\0'; p++)
		{
			if (*p == '/')
			{
				/* make new entry if non-zero (such as at the start of
				 * the path) */
				if (q != p)
				{
					masks[((i - 1) * maxdirs) + cnt] = q;
					cnt++;
				}

				/* terminate part and fold duplicate slashes */
				do
				{
					if (cnt == 1)  /* retain / at start of iargv[i] */
						p++;
					else
						*p++ = '\0';
				}
				while (*p == '/');
				if (*p == '\0')
					break;

				/* start new entry */
				q = p;
			}
		}
		/* write final component, if any */
		if (q != p)
			masks[((i - 1) * maxdirs) + cnt] = q;

		/* brute force cast below values, a pointer hopefully is size_t,
		 * which is large enough to store what we need here */
		p = iargv[i];
		/* set include bit */
		if (*p == '-') {
			masks[((i - 1) * maxdirs) + cnt + 1] = (char *)1;
			p++;
		} else {
			masks[((i - 1) * maxdirs) + cnt + 1] = (char *)0;
		}
		/* set count */
		masks[((i - 1) * maxdirs) + 0] =
			(char *)((*p == '/' ? 1 : -1) * cnt);
	}

#if EBUG
	fprintf(warnout, "applying install masks:\n");
	for (cnt = 0; cnt < masksc; cnt++) {
		ssize_t plen = (ssize_t)masksv[cnt][0];
		fprintf(warnout, "%3zd  ", plen);
		if (plen < 0)
			plen = -plen;
		for (i = 1; i <= plen; i++)
			fprintf(warnout, "%s ", masksv[cnt][i]);
		fprintf(warnout, " %zd\n", (size_t)masksv[cnt][i]);
	}
#endif

	cnt = snprintf(qpth, _Q_PATH_MAX, "%s", CONFIG_EPREFIX);
	cnt--;
	if (qpth[cnt] == '/')
		qpth[cnt] = '\0';

	install_mask_check_dir(masksv, masksc, st, fd, 1, INCLUDE, qpth);

	free(masks);
	free(masksv);
}

static char
qprint_tree_node(
		int            level,
		tree_pkg_ctx  *mpkg,
		tree_pkg_ctx  *bpkg,
		int            replacing)
{
	char            buf[1024];
	int             i;
	char            install_ver[126] = "";
	char            c                = 'N';
	const char     *color;

	if (!pretend)
		return 0;

	if (bpkg == NULL) {
		c = 'N';
		snprintf(buf, sizeof(buf), "%sN%s", GREEN, NORM);
	} else {
		if (bpkg != NULL) {
			switch (replacing) {
				case EQUAL: c = 'R'; break;
				case NEWER: c = 'U'; break;
				case OLDER: c = 'D'; break;
				default:    c = '?'; break;
			}
			snprintf(install_ver, sizeof(install_ver), "[%s%.*s%s] ",
					DKBLUE,
					(int)(sizeof(install_ver) - 4 -
						sizeof(DKBLUE) - sizeof(NORM)),
					tree_pkg_atom(bpkg, false)->PVR, NORM);
		}
		if (update_only && c != 'U')
			return c;
		if ((c == 'R' || c == 'D') && update_only && level)
			return c;
		switch (c) {
			case 'R': color = YELLOW; break;
			case 'U': color = BLUE;   break;
			case 'D': color = DKBLUE; break;
			default:  color = RED;    break;
		}
		snprintf(buf, sizeof(buf), "%s%c%s", color, c, NORM);
#if 0
		if (level) {
			switch (c) {
				case 'N':
				case 'U': break;
				default:
					qprintf("[%c] %d %s\n", c, level, pkg->PF); return;
					break;
			}
		}
#endif
	}

	printf("[%s] ", buf);
	for (i = 0; i < level; ++i)
		putchar(' ');
	{
		const char *rn = qm_nbinrepos > 1 ? qm_repo_name_of_pkg(mpkg) : NULL;
		char        rsuf[80] = "";

		if (rn != NULL)
			snprintf(rsuf, sizeof(rsuf), " %s[%s]%s",
					 qm_repo_tag_color(), rn, NORM);

		if (verbose) {
			char *use = tree_pkg_meta(mpkg, Q_USE);  /* TODO: compute difference */
			printf("%s %s%s%s%s%s%s%s\n",
					atom_format("%[CAT]%[PF]%[SLOT]%[SUBSLOT]%[REPO]",
						tree_pkg_atom(mpkg, true)),
					install_ver, use != NULL ? "(" : "",
					RED, use, NORM, use != NULL ? ")" : "", rsuf);
		} else {
			printf("%s%s\n",
					atom_format("%[CAT]%[PF]%[SLOT]%[SUBSLOT]%[REPO]",
						tree_pkg_atom(mpkg, true)),
					rsuf);
		}
	}
	return c;
}

/* absolute path of the running q binary, so the phase shim can call
 * our own applets (qatom/qlist) without relying on PATH/symlinks */
static const char *
q_self_path(void)
{
	static char buf[_Q_PATH_MAX];

	if (buf[0] == '\0') {
		ssize_t n = readlink("/proc/self/exe", buf, sizeof(buf) - 1);
		if (n <= 0)
			snprintf(buf, sizeof(buf), "q");  /* PATH fallback */
		else
			buf[n] = '\0';
	}
	return buf;
}

/* decompress vdb_path/environment.bz2 (relative to dirfd) into
 * T/environment in-process via libarchive, avoiding external bzip2 */
static int
pkg_unpack_environment(int dirfd, const char *vdb_path, const char *T)
{
	struct archive       *a;
	struct archive_entry *entry;
	char                  path[_Q_PATH_MAX];
	char                  buf[BUFSIZ];
	ssize_t               n;
	int                   fd;
	FILE                 *out;
	int                   ret = -1;

	snprintf(path, sizeof(path), "%s/environment.bz2", vdb_path);
	fd = openat(dirfd, path, O_RDONLY | O_CLOEXEC);
	if (fd < 0)
		return -1;

	if (mkdir_p(T, 0755) != 0) {
		close(fd);
		return -1;
	}
	snprintf(path, sizeof(path), "%s/environment", T);
	out = fopen(path, "w");
	if (out == NULL) {
		close(fd);
		return -1;
	}

	a = archive_read_new();
	archive_read_support_filter_all(a);
	archive_read_support_format_raw(a);
	if (archive_read_open_fd(a, fd, BUFSIZ) == ARCHIVE_OK &&
			archive_read_next_header(a, &entry) == ARCHIVE_OK)
	{
		ret = 0;
		while ((n = archive_read_data(a, buf, sizeof(buf))) > 0) {
			if (fwrite(buf, 1, (size_t)n, out) != (size_t)n) {
				ret = -1;
				break;
			}
		}
		if (n < 0)
			ret = -1;
	}
	archive_read_free(a);
	close(fd);
	fclose(out);
	return ret;
}

/* PMS 9.2 Call order */
enum pkg_phases {
	PKG_PRETEND  = 1,
	PKG_SETUP    = 2,
	/* skipping src_* */
	PKG_PREINST  = 3,
	PKG_POSTINST = 4,
	PKG_PRERM    = 5,
	PKG_POSTRM   = 6
};
#define MAX_EAPI  8
static struct {
	enum pkg_phases phase;
	const char     *phasestr;
	unsigned char   eapi[1 + MAX_EAPI];
} phase_table[] = {
	{ 0,            NULL,           {0,0,0,0,0,0,0,0,0} },   /* align */
	/* phase                   EAPI: 0 1 2 3 4 5 6 7 8 */
	{ PKG_PRETEND,  "pkg_pretend",  {0,0,0,0,1,1,1,1,1} },   /* table 9.3 */
	{ PKG_SETUP,    "pkg_setup",    {1,1,1,1,1,1,1,1,1} },
	{ PKG_PREINST,  "pkg_preinst",  {1,1,1,1,1,1,1,1,1} },
	{ PKG_POSTINST, "pkg_postinst", {1,1,1,1,1,1,1,1,1} },
	{ PKG_PRERM,    "pkg_prerm",    {1,1,1,1,1,1,1,1,1} },
	{ PKG_POSTRM,   "pkg_postrm",   {1,1,1,1,1,1,1,1,1} }
};
static struct {
	enum pkg_phases phase;
	const char     *varname;
} phase_replacingvers[] = {
	{ 0,            NULL                  },   /* align */
	/* phase        varname                  PMS 11.1.2 */
	{ PKG_PRETEND,  "REPLACING_VERSIONS"  },
	{ PKG_SETUP,    "REPLACING_VERSIONS"  },
	{ PKG_PREINST,  "REPLACING_VERSIONS"  },
	{ PKG_POSTINST, "REPLACING_VERSIONS"  },
	{ PKG_PRERM,    "REPLACED_BY_VERSION" },
	{ PKG_POSTRM,   "REPLACED_BY_VERSION" }
};

static void
pkg_run_func_at(
		int             dirfd,
		const char     *vdb_path,
		const char     *phases,
		enum pkg_phases phaseidx,
		const char     *D,
		const char     *T,
		const char     *EAPI,
		const char     *replacing)
{
	const char *func;
	const char *phase;
	char       *script;
	int         eapi;

	/* EAPI officially is a string, but since the official ones are only
	 * numbers, we'll just go with the numbers */
	eapi = (int)strtol(EAPI, NULL, 10);
	if (eapi > MAX_EAPI)
		eapi = MAX_EAPI;  /* let's hope latest known EAPI is closest */

	/* see if this function should be run for the EAPI */
	if (!phase_table[phaseidx].eapi[eapi])
		return;

	/* This assumes no func is a substring of another func.
	 * Today, that assumption is valid for all funcs ...
	 * The phases are the func with the "pkg_" chopped off. */
	func = phase_table[phaseidx].phasestr;
	phase = func + 4;
	if (strstr(phases, phase) == NULL) {
		/* GLEP 65: postinst/preinst QA checks must run even when the
		 * ebuild defines no pkg_(pre|post)inst, matching portage's
		 * separate post-phase hook (postinst_qa_check).  For every other
		 * phase, an undefined func means nothing to do. */
		if (phaseidx != PKG_PREINST && phaseidx != PKG_POSTINST) {
			qprintf("--- %s\n", func);
			return;
		}
	}

	qprintf("@@@ %s\n", func);

	if (pkg_unpack_environment(dirfd, vdb_path, T) != 0) {
		warn("cannot unpack %s/environment.bz2, skipping %s",
			 vdb_path, func);
		return;
	}

	xasprintf(&script,
		/* Provide the funcs the PMS defines as package-manager supplied
		 * (PMS chapter 12): these are exactly the ones portage's
		 * save-ebuild-env.sh strips from environment.bz2 before saving.
		 * Eclass-defined functions are preserved inside the environment
		 * and need no repo/eclass access here.  The environment is
		 * sourced after these definitions, so where an EAPI < 7 env
		 * saved its own copies (e.g. eapi7-ver.eclass) those win. */
		"QBIN='%1$s'\n"
		"debug-print() { :; }\n"
		"debug-print-function() { :; }\n"
		"debug-print-section() { :; }\n"
		/* no sandbox under qmerge: accept and ignore */
		"addread() { :; }\n"
		"addwrite() { :; }\n"
		"adddeny() { :; }\n"
		"addpredict() { :; }\n"
		"register_die_hook() { :; }\n"
		"register_success_hook() { :; }\n"
		"inherit() { die \"inherit is not available during binpkg merge\"; }\n"
		/* output helpers: info to stdout, problems to stderr, like portage */
		"elog() { printf ' * %%b\\n' \"$*\"; }\n"
		"einfo() { elog \"$@\"; }\n"
		"einfon() { printf ' * %%b' \"$*\"; }\n"
		"ewarn() { printf ' * %%b\\n' \"$*\" >&2; }\n"
		"eqawarn() { ewarn \"$@\"; }\n"
		"eerror() { printf ' * %%b\\n' \"$*\" >&2; }\n"
		/* GLEP 65: __eqaquote/eqatag record structured QA tags to
		 * ${T}/qa.log (faithful port of portage isolated-functions.sh) */
		"__eqaquote() { local v=${1} esc='';\n"
		"v=${v//\\\\/\\\\\\\\}; v=${v//\\\"/\\\\\\\"};\n"
		"while read -r; do echo -n \"${esc}${REPLY}\"; esc='\\n'; done <<<\"${v}\"; }\n"
		"eqatag() { local tag i filenames=() data=() verbose=;\n"
		"if [ \"$1\" = -v ]; then verbose=1; shift; fi;\n"
		"tag=$1; shift; [ -n \"$tag\" ] || { die \"eqatag: no tag specified\"; return 1; };\n"
		"for i in \"$@\"; do\n"
		"if [[ ${i} == /* ]]; then filenames+=(\"$i\"); [ -n \"$verbose\" ] && eqawarn \"  ${i}\";\n"
		"elif [[ ${i} == *=* ]]; then data+=(\"$i\");\n"
		"else die \"eqatag: invalid parameter: ${i}\"; return 1; fi; done;\n"
		"{ echo \"- tag: ${tag}\";\n"
		"if [ ${#data[@]} -gt 0 ]; then echo \"  data:\";\n"
		"for i in \"${data[@]}\"; do echo \"    ${i%%%%=*}: \\\"$(__eqaquote \"${i#*=}\")\\\"\"; done; fi;\n"
		"if [ ${#filenames[@]} -gt 0 ]; then echo \"  files:\";\n"
		"for i in \"${filenames[@]}\"; do echo \"    - \\\"$(__eqaquote \"${i}\")\\\"\"; done; fi;\n"
		"} >> \"${T}/qa.log\" 2>/dev/null; }\n"
		/* GLEP 65: run ${phase}-qa-check.d, highest-priority file per
		 * basename, each in a subshell via source; checks may not die.
		 * The repo metadata/-qa-check.d source is intentionally omitted:
		 * portage sets PORTAGE_ECLASS_LOCATIONS empty for binary merges
		 * (verified), so it too runs only these filesystem sources. */
		"__qmerge_qa_check() { local ph=$1 d f paths qa=();\n"
		"cd \"${EROOT:-/}\" 2>/dev/null || return 0;\n"
		"export PORTAGE_QA_PHASE=$ph;\n"
		"paths=( /usr/local/lib/${ph}-qa-check.d /usr/lib/${ph}-qa-check.d /usr/lib/portage/${ph}-qa-check.d );\n"
		"[ -n \"${PORTAGE_BIN_PATH}\" ] && paths+=( \"${PORTAGE_BIN_PATH}/${ph}-qa-check.d\" );\n"
		"for d in \"${paths[@]}\"; do for f in \"$d\"/*; do [ -f \"$f\" ] && qa+=( \"${f##*/}\" ); done; done;\n"
		"[ ${#qa[@]} -eq 0 ] && return 0;\n"
		"while IFS= read -r f; do [ -n \"$f\" ] || continue;\n"
		"for d in \"${paths[@]}\"; do [ -f \"$d/$f\" ] && break; done;\n"
		"( _IN_INSTALL_QA_CHECK=1; source \"$d/$f\" || eerror \"Post-${ph} QA check $f failed to run\" );\n"
		"done < <(printf '%%s\\n' \"${qa[@]}\" | LC_ALL=C sort -u); }\n"
		"ebegin() { printf ' * %%b ...' \"$*\"; }\n"
		"eend() { local r=${1:-$?}; [ $# -gt 0 ] && shift; "
			"if [ ${r} -eq 0 ]; then printf ' [ ok ]\\n'; "
			"else [ -n \"$*\" ] && eerror \"$*\"; printf ' [ !! ]\\n' >&2; fi; "
			"return ${r}; }\n"
		/* die/nonfatal with PMS `die -n` semantics */
		"die() { "
			"if [ \"$1\" = -n ]; then shift; "
				"if [ \"${PORTAGE_NONFATAL:-0}\" = 1 ]; then "
					"[ $# -gt 0 ] && eerror \"$*\"; return 1; fi; fi; "
			"eerror \"ERROR: ${CATEGORY}/${PF}: ${EBUILD_PHASE_FUNC:-?}: "
				"${*:-(no error message)}\"; exit 1; }\n"
		"nonfatal() { PORTAGE_NONFATAL=1 \"$@\"; }\n"
		"__helpers_die() { if [ \"${PORTAGE_NONFATAL:-0}\" = 1 ]; then "
			"eerror \"$*\"; return 1; else die \"$*\"; fi; }\n"
		"assert() { local x s=${PIPESTATUS[*]}; "
			"for x in ${s}; do [ \"${x}\" -eq 0 ] || die \"$@\"; done; }\n"
		/* use/has family */
		"has() { local h=$1; shift; "
			"case \" $* \" in *\" ${h} \"*) return 0;; esac; return 1; }\n"
		"hasq() { has \"$@\"; }\n"
		"hasv() { has \"$@\" && echo \"$1\"; }\n"
		"use() { local u=$1 n=0; case ${u} in !*) n=1; u=${u#!};; esac; "
			"if has \"${u}\" ${USE}; then return ${n}; "
			"else return $((1 - n)); fi; }\n"
		"useq() { use \"$@\"; }\n"
		"usev() { if use \"$1\"; then echo \"${2:-${1#!}}\"; fi; }\n"
		"usex() { use \"$1\" && echo \"${2-yes}$4\" || echo \"${3-no}$5\"; }\n"
		"use_with() { if use \"$1\"; then echo \"--with-${2:-$1}${3:+=$3}\"; "
			"else echo \"--without-${2:-$1}\"; fi; }\n"
		"use_enable() { if use \"$1\"; then echo \"--enable-${2:-$1}${3:+=$3}\"; "
			"else echo \"--disable-${2:-$1}\"; fi; }\n"
		"in_iuse() { local u; for u in ${IUSE}; do "
			"[ \"${u#[+-]}\" = \"$1\" ] && return 0; done; return 1; }\n"
		"get_libdir() { local v=LIBDIR_${ABI}; "
			"if [ -n \"${ABI}\" ] && [ -n \"${!v}\" ]; then echo \"${!v}\"; "
			"else echo lib; fi; }\n"
		/* version helpers (PM-provided in EAPI >= 7, PMS 12.3.x);
		 * split version into alternating separator/component arrays,
		 * comparison is delegated to qatom which implements PMS 3.3 */
		"__q_ver_split() { local v=$1 s c; __Q_SEP=(); __Q_COMP=(); "
			"while [ -n \"${v}\" ]; do "
				"s=${v%%%%[0-9a-zA-Z]*}; v=${v#\"${s}\"}; "
				"case ${v} in [0-9]*) c=${v%%%%[!0-9]*};; "
					"*) c=${v%%%%[!a-zA-Z]*};; esac; "
				"v=${v#\"${c}\"}; "
				"__Q_SEP+=(\"${s}\"); __Q_COMP+=(\"${c}\"); "
				"[ -z \"${s}${c}\" ] && break; done; }\n"
		"ver_cut() { local r=$1 v=${2-${PV}} b e i o=; __q_ver_split \"${v}\"; "
			"b=${r%%%%-*}; case ${r} in *-*) e=${r#*-};; *) e=${b};; esac; "
			"[ \"${b}\" -lt 1 ] && b=1; "
			"if [ -z \"${e}\" ] || [ \"${e}\" -gt ${#__Q_COMP[@]} ]; then "
				"e=${#__Q_COMP[@]}; fi; "
			"for ((i=b; i<=e; i++)); do "
				"[ -n \"${__Q_COMP[i-1]}\" ] || continue; "
				"[ -n \"${o}\" ] && o+=${__Q_SEP[i-1]}; "
				"o+=${__Q_COMP[i-1]}; done; "
			"printf '%%s\\n' \"${o}\"; }\n"
		"ver_rs() { local r b e i rep v o=; "
			"if [ $(($# %% 2)) -eq 1 ]; then v=${@: -1}; "
				"set -- \"${@:1:$#-1}\"; else v=${PV}; fi; "
			"__q_ver_split \"${v}\"; "
			"while [ $# -ge 2 ]; do r=$1 rep=$2; shift 2; "
				"b=${r%%%%-*}; case ${r} in *-*) e=${r#*-};; *) e=${b};; esac; "
				"if [ -z \"${e}\" ] || [ \"${e}\" -ge ${#__Q_SEP[@]} ]; then "
					"e=$((${#__Q_SEP[@]} - 1)); fi; "
				"for ((i=b; i<=e; i++)); do "
					"if [ ${i} -eq 0 ]; then "
						"[ -n \"${__Q_SEP[0]}\" ] && __Q_SEP[0]=${rep}; "
					"else __Q_SEP[i]=${rep}; fi; done; done; "
			"for ((i=0; i<${#__Q_COMP[@]}; i++)); do "
				"o+=${__Q_SEP[i]}${__Q_COMP[i]}; done; "
			"printf '%%s\\n' \"${o}\"; }\n"
		"ver_test() { local v1 op v2 r; "
			"case $# in 2) v1=${PVR} op=$1 v2=$2;; "
				"3) v1=$1 op=$2 v2=$3;; "
				"*) die \"ver_test: bad number of arguments\";; esac; "
			"r=$(\"${QBIN}\" qatom -c \"cat/pkg-${v1}\" \"cat/pkg-${v2}\"); "
			"set -- ${r}; r=$2; "
			"[ -n \"${r}\" ] || die \"ver_test: cannot compare ${v1} ${v2}\"; "
			"case ${op} in "
				"-eq) [ \"${r}\" = '==' ];; "
				"-ne) [ \"${r}\" != '==' ];; "
				"-lt) [ \"${r}\" = '<' ];; "
				"-le) [ \"${r}\" = '<' ] || [ \"${r}\" = '==' ];; "
				"-gt) [ \"${r}\" = '>' ];; "
				"-ge) [ \"${r}\" = '>' ] || [ \"${r}\" = '==' ];; "
				"*) die \"ver_test: invalid operator ${op}\";; esac; }\n"
		/* VDB queries against the right root (-b/-d/-r, PMS 12.3.4) */
		"best_version() { local r=${ROOT:-/}; "
			"case $1 in -r) shift;; -d) r=${SYSROOT:-/}; shift;; "
				"-b|--host-root) r=/; shift;; esac; "
			"\"${QBIN}\" qlist --root \"${r}\" -ICqev \"$1\"; }\n"
		"has_version() { [ -n \"$(best_version \"$@\")\" ]; }\n"
		/* `default` is valid in every phase; all pkg_* defaults are no-ops */
		"default() { :; }\n"
		"default_pkg_pretend() { :; }\n"
		"default_pkg_setup() { :; }\n"
		"default_pkg_preinst() { :; }\n"
		"default_pkg_postinst() { :; }\n"
		"default_pkg_prerm() { :; }\n"
		"default_pkg_postrm() { :; }\n"
		/* install helpers permitted in pkg_* phases, acting on ${ED} */
		"dodir() { local d; for d in \"$@\"; do "
			"mkdir -p \"${ED%%/}/${d#/}\" || __helpers_die \"dodir ${d} failed\"; "
			"done; }\n"
		"keepdir() { local d; dodir \"$@\" || return; for d in \"$@\"; do "
			"touch \"${ED%%/}/${d#/}/.keep_${CATEGORY}_${PN}-${SLOT%%/*}\" "
			"|| __helpers_die \"keepdir ${d} failed\"; done; }\n"
		"fowners() { local f a=$1; shift; for f in \"$@\"; do "
			"chown ${a} \"${ED%%/}/${f#/}\" || __helpers_die \"fowners ${f} failed\"; "
			"done; }\n"
		"fperms() { local f a=$1; shift; for f in \"$@\"; do "
			"chmod ${a} \"${ED%%/}/${f#/}\" || __helpers_die \"fperms ${f} failed\"; "
			"done; }\n"
		"emake() { ${MAKE:-make} ${MAKEOPTS} \"$@\" "
			"|| __helpers_die \"emake failed\"; }\n"
		/* minimal portageq for the queries seen in pkg_* phases */
		"portageq() { local c=$1; shift; case ${c} in "
			"has_version) [ $# -gt 1 ] && shift; has_version \"$1\";; "
			"best_version) [ $# -gt 1 ] && shift; best_version \"$1\";; "
			"envvar) [ \"$1\" = -v ] && shift; printf '%%s\\n' \"${!1}\";; "
			"*) eerror \"portageq: unsupported command ${c}\"; return 1;; "
			"esac; }\n"
		/* Pin the phase locale to a guaranteed-present one BEFORE sourcing:
		 * a binpkg's environment carries the build host's LANG/LC_*
		 * (e.g. en_GB.UTF-8) which a minimal ROOT lacks, and LC_ALL set
		 * here overrides those assignments so bash never setlocale's them
		 * (that's the "cannot change locale" spam).  Default C is the only
		 * locale glibc ALWAYS has built in; C.UTF-8 needs a glibc built with
		 * it or generated locales, absent in a minimal ROOT.  Override with
		 * QMERGE_PHASE_LOCALE=C.UTF-8 etc. where that locale exists. */
		"export LC_ALL=\"${QMERGE_PHASE_LOCALE:-C}\"\n"
		/* Load the main env (unpacked by pkg_unpack_environment) */
		". \"%6$s/environment\"\n"
		/* Reload env vars that matter to us; EBUILD_PHASE must be
		 * re-exported after sourcing, since the environment carries
		 * the stale build-time phase */
		"export EBUILD_PHASE='%3$s'\n"
		"export EBUILD_PHASE_FUNC='%2$s'\n"
		"unset PORTAGE_NONFATAL\n"
		"export FILESDIR=/.does/not/exist/anywhere\n"
		"export MERGE_TYPE=binary\n"
		/* PMS: EAPI <7 ROOT/EROOT carry a trailing slash; EAPI >=7 they
		 * do NOT, and are the EMPTY string for the native root, eclass
		 * code tests [[ -n ${ROOT} ]] for cross-installs (gcc skipped
		 * its eselect compiler-shadow update under a wrong ROOT=/) */
		"case \"${EAPI:-0}\" in\n"
		"0|1|2|3|4|5|6) export ROOT='%4$s'; "
			"export EROOT=\"${ROOT%%/}${EPREFIX%%/}/\" ;;\n"
		"*) ROOT='%4$s'; ROOT=\"${ROOT%%/}\"; export ROOT; "
			"EROOT=\"${ROOT}${EPREFIX%%/}\"; export EROOT ;;\n"
		"esac\n"
		/* BROOT, SYSROOT, ESYSROOT: PMS table 8.3 Prefix values for DEPEND */
		"export BROOT=\n"
		"export SYSROOT=\"${ROOT}\"\n"
		"export ESYSROOT=\"${EROOT}\"\n"
		"export D=\"%5$s\"\n"
		"export ED=\"${D%%/}${EPREFIX%%/}/\"\n"
		"export T=\"%6$s\"\n"
		/* we do not support preserve-libs yet, so force
		 * preserve_old_lib instead; POSIX word loop, not bash pattern
		 * substitution, so the /bin/sh fallback shell can run this */
		"__qm_feat=; for __qm_f in ${FEATURES}; do "
			"[ \"${__qm_f}\" = preserve-libs ] || "
			"__qm_feat=\"${__qm_feat} ${__qm_f}\"; done\n"
		"export FEATURES=\"${__qm_feat# }\"; unset __qm_feat __qm_f\n"
		/* replacing versions: we ignore EAPI availability, for it will
		 * never hurt */
		"export %7$s=\"%8$s\"\n"
		/* Run the phase func only when it is actually defined, for a
		 * pkg with no pkg_(pre|post)inst we still reach here (to run QA).
		 * The function's RETURN value is deliberately ignored, exactly
		 * like portage: ebuilds routinely end phases with `use foo &&
		 * bar` (gcc's pkg_setup does), so nonzero returns are benign;
		 * only die (which exits the shell) signals real failure and is
		 * handled by the caller via the shell's exit status */
		"%9$scommand -v %2$s >/dev/null 2>&1 && %2$s\n"
		/* GLEP 65: after (pre|post)inst, run the QA checks (never fatal) */
		"case ${EBUILD_PHASE} in preinst|postinst) "
			"__qmerge_qa_check ${EBUILD_PHASE};; esac\n"
		/* Ignore func return values (not exit values) */
		":",
		/*1*/ q_self_path(),
		/*2*/ func,
		/*3*/ phase,
		/*4*/ portroot,
		/*5*/ D,
		/*6*/ T,
		/*7*/ phase_replacingvers[phaseidx].varname,
		/*8*/ replacing,
		/*9*/ debug ? "set -x;" : "");
	{
		int prc = xsystem_status(script, dirfd);

		/* die exits the shim shell nonzero; portage semantics: the
		 * gating phases abort the merge, the post-decision phases
		 * warn loudly but continue (silence here is how a broken
		 * pkg_postinst goes unnoticed until something like a missing
		 * compiler symlink bites much later) */
		if (prc != 0) {
			if (strcmp(func, "pkg_pretend") == 0 ||
					strcmp(func, "pkg_setup") == 0 ||
					strcmp(func, "pkg_preinst") == 0)
				err("!!! %s died with status %d, aborting merge",
					func, prc);
			warn("!!! %s died with status %d (continuing)", func, prc);
		}
	}
	free(script);
}
#define pkg_run_func(...) pkg_run_func_at(AT_FDCWD, __VA_ARGS__)

/* Copy one tree (the single package) to another tree (ROOT) */
static int
merge_tree_at(int fd_src, const char *src, int fd_dst, const char *dst,
              FILE *contents, size_t eprefix_len, set **objs, char **cpathp,
              int cp_argc, char **cp_argv, int cpm_argc, char **cpm_argv)
{
	int i, ret, subfd_src, subfd_dst;
	DIR *dir;
	struct dirent *de;
	struct stat st;
	char *cpath;
	size_t clen, nlen, mnlen;

	ret = -1;

	/* Get handles to these subdirs */
	/* Cannot use O_PATH as we want to use fdopendir() */
	subfd_src = openat(fd_src, src, O_RDONLY|O_CLOEXEC);
	if (subfd_src < 0)
		return ret;
	subfd_dst = openat(fd_dst, dst, O_RDONLY|O_CLOEXEC|O_PATH);
	if (subfd_dst < 0) {
		close(subfd_src);
		return ret;
	}

	i = dup(subfd_src);  /* fdopendir closes its argument */
	dir = fdopendir(i);
	if (!dir)
		goto done;

	cpath = *cpathp;
	clen = strlen(cpath);
	cpath[clen] = '/';
	nlen = mnlen = 0;

	while ((de = readdir(dir)) != NULL) {
		const char *name = de->d_name;

		if (filter_self_parent(de) == 0)
			continue;

		/* Build up the full path for this entry */
		nlen = strlen(name);
		if (mnlen < nlen) {
			cpath = *cpathp = xrealloc(*cpathp, clen + 1 + nlen + 1);
			mnlen = nlen;
		}
		strcpy(cpath + clen + 1, name);

		/* Find out what the source path is */
		if (fstatat(subfd_src, name, &st, AT_SYMLINK_NOFOLLOW)) {
			warnp("could not read %s", cpath);
			continue;
		}

		/* Migrate a directory */
		if (S_ISDIR(st.st_mode)) {
			if (!pretend && mkdirat(subfd_dst, name, st.st_mode)) {
				if (errno != EEXIST) {
					warnp("could not create %s", cpath);
					continue;
				}

				/* DDD: update times of dir ? */
			}

			/* syntax: dir dirname */
			if (!pretend)
				fprintf(contents, "dir %s\n", cpath);
			*objs = add_set(cpath, *objs);
			qprintf("%s---%s %s%s%s/\n", GREEN, NORM, DKBLUE, cpath, NORM);

			/* Copy all of these contents */
			merge_tree_at(subfd_src, name,
					subfd_dst, name, contents, eprefix_len,
					objs, cpathp, cp_argc, cp_argv, cpm_argc, cpm_argv);
			cpath = *cpathp;
			mnlen = 0;

			/* In case we didn't install anything, prune the empty dir */
			if (!pretend)
				unlinkat(subfd_dst, name, AT_REMOVEDIR);
		} else if (S_ISREG(st.st_mode)) {
			/* Migrate a file */
			char *hash;
			const char *dname;
			char buf[_Q_PATH_MAX * 2];
			struct stat ignore;

			/* syntax: obj filename hash mtime */
			hash = hash_file_at(subfd_src, name, HASH_MD5);
			if (!pretend)
				fprintf(contents, "obj %s %s %zu""\n",
					cpath, hash ? hash : "xxx", (size_t)st.st_mtime);

			/* Check CONFIG_PROTECT */
			if (config_protected(cpath + eprefix_len,
						cp_argc, cp_argv, cpm_argc, cpm_argv) &&
					fstatat(subfd_dst, name, &ignore, AT_SYMLINK_NOFOLLOW) == 0)
			{
				/* ._cfg####_ */
				char *num;
				dname = buf;
				snprintf(buf, sizeof(buf), "._cfg####_%s", name);
				num = buf + 5;
				for (i = 0; i < 10000; ++i) {
					sprintf(num, "%04i", i);
					num[4] = '_';
					if (fstatat(subfd_dst, dname, &ignore, AT_SYMLINK_NOFOLLOW))
						break;
				}
				qprintf("%s>>>%s %s (%s)\n", GREEN, NORM, cpath, dname);
			} else {
				dname = name;
				qprintf("%s>>>%s %s\n", GREEN, NORM, cpath);
			}
			*objs = add_set(cpath, *objs);

			if (pretend)
				continue;

			if (move_file(subfd_src, name, subfd_dst, dname, &st) != 0)
				warnp("failed to move file from %s", cpath);
		} else if (S_ISLNK(st.st_mode)) {
			/* Migrate a symlink */
			size_t len = st.st_size;
			char sym[_Q_PATH_MAX];

			/* Find out what we're pointing to */
			if (readlinkat(subfd_src, name, sym, sizeof(sym)) == -1) {
				warnp("could not read link %s", cpath);
				continue;
			}
			sym[len < _Q_PATH_MAX ? len : _Q_PATH_MAX - 1] = '\0';

			/* syntax: sym src -> dst mtime */
			if (!pretend)
				fprintf(contents, "sym %s -> %s %zu\n",
						cpath, sym, (size_t)st.st_mtime);
			qprintf("%s>>>%s %s%s -> %s%s\n", GREEN, NORM,
					CYAN, cpath, sym, NORM);
			*objs = add_set(cpath, *objs);

			if (pretend)
				continue;

			/* Make it in the dest tree */
			if (symlinkat(sym, subfd_dst, name)) {
				/* If the symlink exists, unlink it and try again */
				if (errno != EEXIST ||
				    unlinkat(subfd_dst, name, 0) ||
				    symlinkat(sym, subfd_dst, name)) {
					warnp("could not create link %s to %s", cpath, sym);
					continue;
				}
			}

			struct timespec times[2];
			times[0] = get_stat_atime(&st);
			times[1] = get_stat_mtime(&st);
			utimensat(subfd_dst, name, times, AT_SYMLINK_NOFOLLOW);
		} else {
			/* WTF is this !? */
			warnp("unknown file type %s", cpath);
			continue;
		}
	}

	closedir(dir);
	ret = 0;

 done:
	close(subfd_src);
	close(subfd_dst);

	return ret;
}

static void
pkg_extract_xpak_cb(
	void *ctx,
	char *pathname,
	int pathname_len,
	int data_offset,
	int data_len,
	char *data)
{
	FILE *out;
	int *destdirfd = (int *)ctx;
	(void)pathname_len;

	int fd = openat(*destdirfd, pathname,
			O_WRONLY | O_CLOEXEC | O_CREAT | O_TRUNC, 0644);
	if (fd < 0)
		return;
	out = fdopen(fd, "w");
	if (!out)
		return;

	fwrite(data + data_offset, 1, data_len, out);

	fclose(out);
}

/* bounded reader so libarchive only sees the tar bytes preceding the
 * xpak trailer of a tbz2 */
struct qm_tar_stream {
	FILE  *f;
	size_t left;
	char   buf[BUFSIZ];
};

static la_ssize_t
qm_tar_read_cb(struct archive *a, void *ud, const void **bufp)
{
	struct qm_tar_stream *s = ud;
	size_t n = s->left < sizeof(s->buf) ? s->left : sizeof(s->buf);

	(void)a;
	if (n > 0)
		n = fread(s->buf, 1, n, s->f);
	s->left -= n;
	*bufp = s->buf;
	return (la_ssize_t)n;
}

/* ---- resolver S1: atom satisfaction incl. USE-dep constraints ---- */

/* whitespace-separated flag string -> set; leading +/- (IUSE style) is
 * stripped so USE and IUSE compare on the bare flag name */
static set *
qm_flags_to_set(const char *str)
{
	set  *s = create_set();
	char *tmp;
	char *tok;
	char *sp;

	if (str == NULL)
		return s;
	tmp = xstrdup(str);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok != '\0')
			add_set_unique(tok, s, NULL);
	}
	free(tmp);
	return s;
}

/* evaluate one [..]-style USE-dep element against a candidate's USE/IUSE.
 * puse is the depending package's USE (for the ?/= conditional forms),
 * may be NULL at the resolution root. */
static bool
qm_usedep_ok(const atom_usedep *ud, set *cuse, set *ciuse, set *puse)
{
	const char *f       = ud->use;
	bool        in_use  = contains_set(f, cuse) != NULL;
	bool        in_iuse = contains_set(f, ciuse) != NULL;
	bool        eff;

	/* parent-conditional forms reference the depending pkg's USE */
	if (ud->sfx_cond == ATOM_UC_COND || ud->sfx_cond == ATOM_UC_EQUAL) {
		bool pon = puse != NULL && contains_set(f, puse) != NULL;
		bool neg = ud->pfx_cond == ATOM_UC_NOT;

		if (ud->sfx_cond == ATOM_UC_EQUAL)      /* [flag=] / [!flag=] */
			return neg ? (in_use != pon) : (in_use == pon);
		/* [flag?]: require cand-on when parent-on;
		 * [!flag?]: require cand-on when parent-off */
		if (neg)
			return pon ? true : in_use;
		return pon ? in_use : true;
	}

	/* effective state, honouring the (+)/(-) default when the flag is
	 * absent from the candidate's IUSE */
	if (in_use)
		eff = true;
	else if (in_iuse)
		eff = false;
	else if (ud->sfx_cond == ATOM_UC_PREV_ENABLED)   /* (+) */
		eff = true;
	else if (ud->sfx_cond == ATOM_UC_PREV_DISABLED)  /* (-) */
		eff = false;
	else
		return false;   /* no default and not in IUSE: unsatisfiable */

	/* [-flag] wants it disabled; plain [flag] wants it enabled */
	return ud->pfx_cond == ATOM_UC_NEG ? !eff : eff;
}

/* does candidate package cand satisfy dependency atom dep? */
static bool
atom_satisfied_by(atom_ctx *dep, tree_pkg_ctx *cand, set *parent_use)
{
	atom_ctx *ca = tree_pkg_atom(cand, dep->SLOT != NULL);

	/* category/PN/version/operator/slot/subslot via the standard
	 * matcher (subslot now compares by effective value); a ::@binrepo
	 * selector is NOT an ebuild-repo constraint, ignore REPO for it
	 * (best_version already restricted the walk) */
	if (atom_compare_flg(ca, dep,
			dep->REPO != NULL && dep->REPO[0] == '@' ?
			ATOM_COMP_DEFAULT | ATOM_COMP_NOREPO : ATOM_COMP_DEFAULT)
			!= EQUAL)
		return false;

	/* USE-deps are not covered by atom_compare; check them here */
	if (dep->usedeps != NULL) {
		set               *cuse  = qm_flags_to_set(tree_pkg_meta(cand, Q_USE));
		set               *ciuse = qm_flags_to_set(tree_pkg_meta(cand, Q_IUSE));
		const atom_usedep *ud;
		bool               ok    = true;

		for (ud = dep->usedeps; ud != NULL; ud = ud->next)
			if (!qm_usedep_ok(ud, cuse, ciuse, parent_use)) {
				ok = false;
				break;
			}
		free_set(cuse);
		free_set(ciuse);
		if (!ok)
			return false;
	}
	return true;
}

/* self-test of the USE-dep logic, triggered by QMERGE_SELFTEST=1; prints
 * PASS/FAIL lines and returns the failure count */
static int
qm_resolver_selftest(void)
{
	int   fails = 0;
	set  *use;
	set  *iuse;
	struct { const char *desc; const char *dep; const char *use;
			 const char *iuse; const char *puse; bool want; } cases[] = {
		/* plain [flag] */
		{ "[a] with a on",        "c/p[a]",    "a b",  "a b",  NULL, true  },
		{ "[a] with a off",       "c/p[a]",    "b",    "a b",  NULL, false },
		{ "[-a] with a off",      "c/p[-a]",   "b",    "a b",  NULL, true  },
		{ "[-a] with a on",       "c/p[-a]",   "a",    "a b",  NULL, false },
		/* (+)/(-) defaults for flag absent from IUSE */
		{ "[a(+)] a not in IUSE", "c/p[a(+)]", "b",    "b",    NULL, true  },
		{ "[a(-)] a not in IUSE", "c/p[a(-)]", "b",    "b",    NULL, false },
		{ "[a] a not in IUSE",    "c/p[a]",    "b",    "b",    NULL, false },
		/* multi */
		{ "[a,-b] both ok",       "c/p[a,-b]", "a",    "a b",  NULL, true  },
		{ "[a,-b] b on -> fail",  "c/p[a,-b]", "a b",  "a b",  NULL, false },
		/* python_targets real-world shape */
		{ "py314(+) enabled",  "d/r[python_targets_python3_14(+)]",
		  "python_targets_python3_14", "python_targets_python3_14", NULL, true },
		{ "py314(+) missing -> fail (in IUSE, off)",
		  "d/r[python_targets_python3_14(+)]",
		  "python_targets_python3_12", "python_targets_python3_12 python_targets_python3_14",
		  NULL, false },
		/* parent-conditional = */
		{ "[a=] parent on cand on",  "c/p[a=]", "a", "a", "a", true  },
		{ "[a=] parent on cand off", "c/p[a=]", "b", "a b", "a", false },
		{ "[!a=] parent on cand off","c/p[!a=]","b", "a b", "a", true  },
	};
	size_t i;

	for (i = 0; i < ARRAY_SIZE(cases); i++) {
		atom_ctx *dep = atom_explode(cases[i].dep);
		bool      got;
		set      *pu  = cases[i].puse != NULL ?
						qm_flags_to_set(cases[i].puse) : NULL;
		bool      ok  = true;
		const atom_usedep *ud;

		use  = qm_flags_to_set(cases[i].use);
		iuse = qm_flags_to_set(cases[i].iuse);
		for (ud = dep->usedeps; ud != NULL; ud = ud->next)
			if (!qm_usedep_ok(ud, use, iuse, pu)) {
				ok = false;
				break;
			}
		got = ok;
		printf("%s %-40s (want=%d got=%d)\n",
			   got == cases[i].want ? "PASS" : "FAIL",
			   cases[i].desc, cases[i].want, got);
		if (got != cases[i].want)
			fails++;
		free_set(use);
		free_set(iuse);
		if (pu != NULL)
			free_set(pu);
		atom_implode(dep);
	}
	printf("selftest: %d failure(s)\n", fails);
	return fails;
}

/* ---- resolver S2: || (any-of) choice via dep_zapdeps ranking ---- */

enum {
	QM_RANK_INSTALLED = 0,   /* every atom satisfied by an installed pkg */
	QM_RANK_AVAILABLE = 1,   /* every atom satisfiable via a binpkg      */
	QM_RANK_OTHER     = 2,   /* not fully satisfiable                    */
};

/* classify one || branch: is it fully satisfied by installed packages,
 * merely available via binpkgs, or unsatisfiable?  New-style virtual
 * category atoms have portage's zero-cost semantics (a missing provider
 * does not make the branch unavailable, nor count as installed). */
static int
qm_choice_rank(dep_node_t *choice, set *parent_use)
{
	array    *atoms = dep_flatten_tree(choice);
	size_t    i;
	atom_ctx *a;
	bool      all_inst  = true;
	bool      all_avail = true;

	array_for_each(atoms, i, a) {
		tree_pkg_ctx *inst;
		tree_pkg_ctx *bin;
		bool          isat;
		bool          bsat;
		bool          is_virtual;

		if (a->blocker != ATOM_BL_NONE)
			continue;

		inst = best_version(a, BV_INSTALLED);
		_qm_bv_parent_use = parent_use;
		bin  = best_version(a, BV_BINPKG);
		_qm_bv_parent_use = NULL;
		isat = inst != NULL && atom_satisfied_by(a, inst, parent_use);
		bsat = bin  != NULL && atom_satisfied_by(a, bin, parent_use);
		is_virtual = a->CATEGORY != NULL &&
					 strcmp(a->CATEGORY, "virtual") == 0;

		if (!isat)
			all_inst = false;
		if (!isat && !bsat && !is_virtual)
			all_avail = false;
	}
	array_free(atoms);

	if (all_inst)
		return QM_RANK_INSTALLED;
	if (all_avail)
		return QM_RANK_AVAILABLE;
	return QM_RANK_OTHER;
}

/* choose one branch of an || group, mirroring portage dep_zapdeps: the
 * best-ranked branch wins, ties broken by source order (first).  An
 * already-installed-satisfied branch (e.g. the installed alternative of
 * || ( zlib zlib-ng )) is preferred so the other is never pulled. */
static dep_node_t *
zapdeps_pick(dep_node_t *any, set *parent_use)
{
	array      *choices = dep_node_children(any);
	size_t      i;
	dep_node_t *node;
	dep_node_t *best      = NULL;
	int         best_rank = QM_RANK_OTHER + 1;

	array_for_each(choices, i, node) {
		int r = qm_choice_rank(node, parent_use);

		if (r < best_rank) {
			best_rank = r;
			best      = node;
			if (r == QM_RANK_INSTALLED)
				break;   /* cannot do better; first installed wins */
		}
	}
	return best;
}

/* ---- resolver S3: transitive resolve pass producing a merge plan ---- */

struct qm_plan {
	array *merge;      /* owned cpv (CAT/PF) strings, dependency order */
	set   *in_merge;   /* cpv already appended */
	set   *examined;   /* provider cpv whose deps were walked */
};

static void qm_resolve(atom_ctx *atom, set *parent_use,
					   struct qm_plan *plan, int level);

static void
qm_plan_add(struct qm_plan *plan, const char *cpv)
{
	if (contains_set(cpv, plan->in_merge) != NULL)
		return;
	add_set(cpv, plan->in_merge);
	array_append(plan->merge, xstrdup(cpv));
}

static void
qm_resolve_node(dep_node_t *node, set *parent_use,
				struct qm_plan *plan, int level)
{
	if (node == NULL)
		return;

	switch (dep_node_type(node)) {
	case DEP_ATOM: {
		atom_ctx *a = dep_node_atom(node);

		if (a != NULL)
			qm_resolve(a, parent_use, plan, level);
		break;
	}
	case DEP_ANY: {
		dep_node_t *choice = zapdeps_pick(node, parent_use);

		qm_resolve_node(choice, parent_use, plan, level);
		break;
	}
	default: {
		array      *members = dep_node_children(node);
		size_t      i;
		dep_node_t *child;

		if (members != NULL)
			array_for_each(members, i, child)
				qm_resolve_node(child, parent_use, plan, level);
		break;
	}
	}
}

/* is the binpkg strictly newer (version-wise) than the installed one?  used by
 * -D to decide whether to upgrade an already-satisfied dep.  Ignores subslot/
 * repo, same as the [U] status test in qm_slot_status. */
static bool
qm_bin_newer(tree_pkg_ctx *bin, tree_pkg_ctx *inst)
{
	if (bin == NULL)
		return false;
	if (inst == NULL)
		return true;
	return atom_compare_flg(tree_pkg_atom(bin, false),
							tree_pkg_atom(inst, false),
							ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO) == NEWER;
}

static void
qm_resolve(atom_ctx *atom, set *parent_use, struct qm_plan *plan, int level)
{
	tree_pkg_ctx *inst;
	tree_pkg_ctx *bin;
	tree_pkg_ctx *provider;
	atom_ctx     *patom;
	atom_ctx     *ratom;
	atom_ctx      neut;
	set          *use;
	char          cpv[512];
	char         *rdep;
	char         *pdep;
	char         *usestr;
	bool          pull;
	ssize_t       aff_new = -1;

	if (atom->blocker != ATOM_BL_NONE)
		return;

	inst = best_version(atom, BV_INSTALLED);
	_qm_bv_parent_use = parent_use;
	bin  = best_version(atom, BV_BINPKG);
	_qm_bv_parent_use = NULL;

	if (level == 0) {
		/* an explicitly requested atom is always (re)installed from the
		 * best available binpkg, like `emerge -K <pkg>`, it shows as
		 * [R] when the same version is installed, [U] when newer.  Only
		 * dependencies (level > 0) are skipped when already satisfied. */
		if (bin != NULL && atom_satisfied_by(atom, bin, parent_use)) {
			provider = bin;
			pull     = true;
		} else if (inst != NULL &&
				   atom_satisfied_by(atom, inst, parent_use)) {
			provider = inst;
			pull     = false;
			/* installed through a package move but no binhost carries
			 * the new name yet: keep the installed copy, but say so */
			if (bin == NULL) {
				const char *mh = qm_move_fail_hint(atom);

				if (mh[0] != '\0')
					warn("no binpkg of %s on any binhost%s",
						 atom_to_string(atom), mh);
			}
		} else {
			const char *h  = qm_excl_hint(atom);
			const char *mh = qm_move_fail_hint(atom);

			warn("cannot satisfy %s%s%s", atom_to_string(atom), h, mh);
			return;
		}
	} else if (deep && bin != NULL && atom_satisfied_by(atom, bin, parent_use) &&
			   (qm_bin_newer(bin, inst) ||
				(newuse && inst != NULL && qm_use_changed(bin, inst)) ||
				(rebuilt_bins && inst != NULL &&
				 qm_rebuilt_newer(bin, inst)))) {
		/* -D: proactively upgrade a satisfied dep to a strictly newer binpkg
		 * (never a downgrade), giving `emerge -uD`-style deep updates.
		 * With -N a same-version rebuild whose built USE changed (e.g.
		 * new PYTHON_TARGETS) also counts, like emerge --newuse. */
		provider = bin;
		pull     = true;
	} else if (inst != NULL && atom_satisfied_by(atom, inst, parent_use)) {
		provider = inst;
		pull     = false;
	} else if (bin != NULL && atom_satisfied_by(atom, bin, parent_use)) {
		provider = bin;
		pull     = true;
	} else if (atom->CATEGORY != NULL &&
			   strcmp(atom->CATEGORY, "virtual") == 0) {
		return;   /* new-style virtual, zero-cost, no provider */
	} else {
		const char *h  = qm_excl_hint(atom);
		const char *mh = qm_move_fail_hint(atom);

		warn("cannot satisfy dependency %s%s%s", atom_to_string(atom), h, mh);
		return;
	}

	/* anti-downgrade: a dependency must never pull a provider OLDER than what's
	 * already installed in that slot.  A stale := consumer (built against
	 * foo:0/OLD) otherwise drags foo *down* to OLD to satisfy its subslot bind;
	 * keep the installed provider instead and let the sweep flag the stale
	 * consumer for rebuild.  (level 0 is the explicit target, leave it be.) */
	if (pull && level > 0 && provider == bin && bin != NULL) {
		tree_pkg_ctx *cur;

		ratom = atom;
		if (atom->SUBSLOT != NULL && atom->SUBSLOT != atom->SLOT) {
			neut         = *atom;      /* shallow copy shares all pointers */
			neut.SUBSLOT = neut.SLOT;  /* look up the installed slot occupant */
			ratom        = &neut;
		}
		cur = best_version(ratom, BV_INSTALLED);   /* invalidates inst (used) */
		if (cur != NULL && qm_bin_newer(cur, bin)) {
			provider = cur;   /* installed slot version is newer -> keep it */
			pull     = false;
		}
	}

	/* B1: tree_pkg_ctx from best_version() is backed by a cached tree
	 * and is invalidated by further best_version() calls; copy out
	 * everything we need BEFORE recursing (which makes many such
	 * calls), and carry the cpv, not the ctx, in the plan */
	patom = tree_pkg_atom(provider, false);
	snprintf(cpv, sizeof(cpv), "%s/%s",
			 patom->CATEGORY != NULL ? patom->CATEGORY : "",
			 patom->PF != NULL ? patom->PF : "");
	{
		ssize_t prov_repo = qm_repoidx_of_pkg(provider);

		/* pin the serving binrepo into the plan entry (cpv::@binrepo)
		 * so every downstream =cpv re-resolution (display, prefetch,
		 * fetch, conflict scan) lands on the SAME repo, without
		 * this, a version present on several binhosts re-resolves by
		 * priority and an explicit selection would silently merge the
		 * wrong build */
		if (pull && qm_nbinrepos > 1 && prov_repo >= 0) {
			size_t cl = strlen(cpv);

			snprintf(cpv + cl, sizeof(cpv) - cl, "::@%s",
					 qm_binrepos[prov_repo].name);
		}

		/* pull-time notices: only packages REALLY entering the plan
		 * from a foreign repo get lines, a dep merely evaluated but
		 * satisfied by the installed system stays silent */
		if (pull && prov_repo > 0 &&
				((atom->REPO != NULL && atom->REPO[0] == '@') ||
				 (level > 0 && _qm_repo_affinity == prov_repo)))
		{
			char        key[512];
			char        msg[512];
			char        why[160];
			const char *how = atom->REPO != NULL && atom->REPO[0] == '@'
					? "explicitly requested" : "@repo subtree affinity";

			snprintf(key, sizeof(key), "=%s [%s]",
					 atom_to_string(tree_pkg_atom(provider, true)),
					 qm_binrepos[prov_repo].name);

			if (level > 0 && _qm_repo_affinity == prov_repo) {
				snprintf(msg, sizeof(msg),
						 "pulled as dependency by @%s subtree affinity",
						 qm_binrepos[prov_repo].name);
				qm_notice(key, msg);
			}
			if (!binpkg_use_ok_r(provider, tree_pkg_atom(provider, true),
								 qm_binrepos[prov_repo].name,
								 why, sizeof(why)))
			{
				snprintf(msg, sizeof(msg),
						 "USE mismatch: %s -- proceeding (%s)", why, how);
				qm_notice(key, msg);
			}
		}

		/* explicit @repo target: its whole dep subtree prefers that
		 * repo (consistent island); scoped, restored after the walk */
		if (atom->REPO != NULL && atom->REPO[0] == '@' && prov_repo > 0)
			aff_new = prov_repo;
	}
	usestr = xstrdup(tree_pkg_meta(provider, Q_USE)     ? : "");
	rdep   = xstrdup(tree_pkg_meta(provider, Q_RDEPEND) ? : "");
	pdep   = xstrdup(tree_pkg_meta(provider, Q_PDEPEND) ? : "");
	/* provider ctx must not be used past this point */

	if (contains_set(cpv, plan->examined) != NULL) {
		if (pull)
			qm_plan_add(plan, cpv);
		free(usestr);
		free(rdep);
		free(pdep);
		return;
	}
	add_set(cpv, plan->examined);

	/* descend into dependencies for packages that will be merged (pull) or
	 * the requested atom (level 0).  With -D, descend into everything --
	 * including already-satisfied installed deps, so the whole tree is
	 * checked for updates, matching `emerge --deep`. */
	if ((pull || level == 0 || deep) && follow_rdepends) {
		char    *deps[2];
		int      di;
		ssize_t  aff_save = _qm_repo_affinity;

		/* deps evaluated under the PROVIDER's built USE (an alien
		 * repo's package resolves its subtree with the flags it was
		 * really built with); an explicit @repo target additionally
		 * turns on subtree affinity for the recursion below */
		if (aff_new > 0)
			_qm_repo_affinity = aff_new;

		use = qm_flags_to_set(usestr);
		deps[0] = rdep;
		deps[1] = pdep;
		for (di = 0; di < 2; di++) {
			dep_node_t *t;

			if (deps[di][0] == '\0')
				continue;
			t = dep_grow_tree(deps[di]);
			if (t == NULL)
				continue;
			dep_prune_use(t, use);
			qm_resolve_node(t, use, plan, level + 1);
			dep_burn_tree(t);
		}
		free_set(use);

		_qm_repo_affinity = aff_save;
	}

	/* post-order: append after deps so merge order is deps-first */
	if (pull)
		qm_plan_add(plan, cpv);

	free(usestr);
	free(rdep);
	free(pdep);
}

/* string comparator for array_sort */
static int
qm_strcmp_cb(const void *l, const void *r)
{
	return strcmp(*(char * const *)l, *(char * const *)r);
}

/* portage cpv_expand disambiguation (lib/portage/dbapi/cpv_expand.py):
 * for a bare package name matching several categories, prefer the ones
 * that are NOT acct-user/acct-group/virtual; among those pick the last
 * in sorted category order (as portage's category iteration does).  If
 * every match is an account/virtual package the name is genuinely
 * ambiguous.  Returns an owned "category" string, or NULL if unresolved
 * (0 matches) / ambiguous (caller warns).  *ambiguous set accordingly. */
static char *
qm_pick_category(const char *pn, bool *ambiguous)
{
	atom_ctx     *bare;
	set          *cats;
	array        *catlist;
	array        *matches;
	size_t        i;
	tree_pkg_ctx *pkg;
	char         *cat;
	char         *chosen   = NULL;
	bool          any_acct = false;
	int           tt;

	*ambiguous = false;
	bare = atom_explode(pn);
	if (bare == NULL)
		return NULL;

	cats = create_set();
	/* collect candidate categories from both binpkg and vdb trees */
	for (tt = 0; tt < 2; tt++) {
		tree_ctx *tree = tt == 0 ?
				tree_new(portroot, pkgdir, TREETYPE_BINPKG, true) :
				tree_new(portroot, portvdb, TREETYPE_VDB, true);

		if (tree == NULL)
			continue;
		matches = tree_match_atom(tree, bare,
				TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);
		array_for_each(matches, i, pkg) {
			atom_ctx *pa = tree_pkg_atom(pkg, false);

			if (pa->CATEGORY != NULL)
				add_set_unique(pa->CATEGORY, cats, NULL);
		}
		array_free(matches);
		tree_close(tree);
	}
	atom_implode(bare);

	catlist = set_keys(cats);
	array_sort(catlist, qm_strcmp_cb);
	array_for_each(catlist, i, cat) {
		if (strcmp(cat, "acct-group") == 0 ||
				strcmp(cat, "acct-user") == 0 ||
				strcmp(cat, "virtual") == 0) {
			any_acct = true;
		} else {
			free(chosen);
			chosen = xstrdup(cat);   /* last non-acct/virtual wins */
		}
	}
	array_free(catlist);

	/* chosen NULL + saw account/virtual matches => genuinely ambiguous;
	 * chosen NULL + no acct => name not found at all */
	if (chosen == NULL && any_acct)
		*ambiguous = true;
	free_set(cats);
	return chosen;
}

/* Return the installed VDB packages in cat/pn that occupy the same SLOT
 * as `slot` (NULL/empty treated as "0", per PMS).  Uses a bare cat/pn
 * match plus an explicit SLOT filter rather than a slot-qualified atom,
 * because slot-qualified tree_match_atom does not match reliably here.
 * The returned array must be freed with array_free by the caller; the
 * tree_pkg_ctx elements are owned by the vdb tree and stay valid while it
 * is open. */
static array *
qm_slot_members(const char *cat, const char *pn, const char *slot)
{
	char          buf[_Q_PATH_MAX];
	atom_ctx     *cpn;
	array        *all;
	array        *ret  = array_new();
	tree_ctx     *vdb  = _qmerge_vdb_tree;
	const char   *want = (slot != NULL && slot[0] != '\0') ? slot : "0";
	size_t        n;
	tree_pkg_ctx *m;

	if (cat == NULL || pn == NULL)
		return ret;
	if (vdb == NULL) {
		vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);
		_qmerge_vdb_tree = vdb;
	}
	if (vdb == NULL)
		return ret;

	snprintf(buf, sizeof(buf), "%s/%s", cat, pn);
	cpn = atom_explode(buf);
	if (cpn == NULL)
		return ret;

	all = tree_match_atom(vdb, cpn, TREE_MATCH_DEFAULT);
	if (all != NULL) {
		array_for_each(all, n, m) {
			atom_ctx   *ma = tree_pkg_atom(m, true);  /* full -> reads SLOT */
			const char *ms = (ma->SLOT != NULL && ma->SLOT[0] != '\0') ?
					ma->SLOT : "0";
			if (strcmp(ms, want) == 0)
				array_append(ret, m);
		}
		array_free(all);
	}
	atom_implode(cpn);
	return ret;
}

/* Emerge-style status string for installing binatom: R/U/D vs the LOWEST-
 * versioned member of the SAME slot; N if the pkg isn't installed at all;
 * NS ("new slot") if it lives only in a DIFFERENT slot.  Mirrors portage's
 * slot-based view so the plan matches emerge.  fromver (if non-NULL) gets
 * the replaced version, valid while the vdb tree stays open, else NULL. */
static const char *
qm_slot_status(const atom_ctx *binatom, const char **fromver)
{
	array      *members;
	const char *s = "N";

	if (fromver != NULL)
		*fromver = NULL;
	if (binatom == NULL || binatom->CATEGORY == NULL || binatom->PN == NULL)
		return "N";

	members = qm_slot_members(binatom->CATEGORY, binatom->PN, binatom->SLOT);
	if (members != NULL && array_cnt(members) > 0) {
		size_t         n;
		tree_pkg_ctx  *m;
		atom_ctx      *lowatom = NULL;

		array_for_each(members, n, m) {
			atom_ctx *ma = tree_pkg_atom(m, false);
			if (lowatom == NULL ||
					atom_compare_flg(ma, lowatom, ATOM_COMP_NOSLOT |
						ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO) == OLDER)
				lowatom = ma;
		}
		if (lowatom != NULL) {
			/* members are already in the target slot, so compare VERSION only:
			 * ignore SLOT (the binpkg atom's SLOT may be unread/NULL for some
			 * binpkg formats, a null-vs-"0" would falsely read NOT_EQUAL) and
			 * BUILD_ID (binpkg-multi-instance numbers rebuilds, so build 5 vs
			 * installed build 4 of the SAME version is [R], not a phantom [N]). */
			atom_ctx      bcmp = *binatom;
			atom_equality e;

			bcmp.BUILDID = 0;
			e = atom_compare_flg(&bcmp, lowatom, ATOM_COMP_NOSLOT |
					ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO);
			s = e == NEWER ? "U" :
				e == OLDER ? "D" :
				e == EQUAL ? "R" : "N";
			if (fromver != NULL)
				*fromver = lowatom->PVR;
		}
	} else {
		/* nothing in this slot: if the pkg is installed in a different
		 * slot it's a new-slot install (emerge's NS), else just new */
		char      buf[_Q_PATH_MAX];
		atom_ctx *cpn;

		snprintf(buf, sizeof(buf), "%s/%s",
				binatom->CATEGORY, binatom->PN);
		cpn = atom_explode(buf);
		if (cpn != NULL) {
			if (best_version(cpn, BV_INSTALLED) != NULL)
				s = "NS";
			atom_implode(cpn);
		}
	}
	if (members != NULL)
		array_free(members);
	return s;
}

/* GLEP 42: print the "N news items need reading" notice for each repo,
 * counting unread items already recorded in ${EROOT}var/lib/gentoo/news/
 * news-<repoid>.unread.  Read-only: qmerge does not sync, so it never
 * scans a repo or rewrites the unread list (that is emerge --sync's job);
 * it simply surfaces the current synced state, matching portage's
 * count_unread_news(update=False) + display_news_notifications. */
static void
qm_news_notice(void)
{
	char           dir[_Q_PATH_MAX];
	DIR           *d;
	struct dirent *de;
	bool           any = false;

	snprintf(dir, sizeof(dir), "%svar/lib/gentoo/news", portroot);
	if ((d = opendir(dir)) == NULL)
		return;

	while ((de = readdir(d)) != NULL) {
		const char *nm  = de->d_name;
		size_t      len = strlen(nm);
		size_t      rlen;
		char        path[_Q_PATH_MAX + 280];
		char        repoid[128];
		FILE       *f;
		char       *line = NULL;
		size_t      cap  = 0;
		ssize_t     n;
		int         count = 0;

		/* match news-<repoid>.unread */
		if (strncmp(nm, "news-", 5) != 0)
			continue;
		if (len < 5 + 7 || strcmp(nm + len - 7, ".unread") != 0)
			continue;

		snprintf(path, sizeof(path), "%s/%s", dir, nm);
		if ((f = fopen(path, "r")) == NULL)
			continue;
		/* count non-blank, non-comment lines (portage grabfile semantics) */
		while ((n = getline(&line, &cap, f)) != -1) {
			char *p = line;
			while (*p == ' ' || *p == '\t')
				p++;
			if (*p != '\0' && *p != '\n' && *p != '#')
				count++;
		}
		free(line);
		fclose(f);
		if (count <= 0)
			continue;

		rlen = len - 5 - 7;
		if (rlen >= sizeof(repoid))
			rlen = sizeof(repoid) - 1;
		memcpy(repoid, nm + 5, rlen);
		repoid[rlen] = '\0';

		if (!any) {
			printf("\n");
			any = true;
		}
		printf(" %s*%s IMPORTANT: %d news items need reading for "
				"repository '%s'.\n", YELLOW, NORM, count, repoid);
	}
	closedir(d);

	if (any)
		printf(" %s*%s Use %sqnews read%s to view new items.\n\n",
				YELLOW, NORM, GREEN, NORM);
}

/* progress counter for the "(N of M)" in pkg_download's fetch line; set by
 * qm_prefetch before each fork (inherited by the worker), 0 otherwise so
 * the serial path prints an uncounted "Fetching <pkg>". */
static size_t qm_dl_n, qm_dl_total;

/* (N of M) counters for the merge history records below */
static size_t qm_mg_n, qm_mg_total;

/* portage-parity merge history: qlop-parseable records appended to
 * EMERGE_LOG_DIR/emerge.log (same file, format and perms as portage),
 * so qlop -muv answers "what happened on this box" for qmerge-driven
 * systems too.  Lazily opened on first record; silent on failure
 * (logging must never break a merge). */
static FILE *qm_elogf;

__attribute__((format(printf, 1, 2)))
static void
qm_elog(const char *fmt, ...)
{
	va_list ap;

	if (qm_elogf == NULL) {
		char path[_Q_PATH_MAX];
		int  fd;

		snprintf(path, sizeof(path), "%s/emerge.log", portlogdir);
		fd = open(path, O_WRONLY | O_APPEND | O_CREAT | O_CLOEXEC, 0660);
		if (fd < 0)
			return;
		{
			struct group *gr = getgrnam("portage");

			if (gr != NULL && fchown(fd, 0, gr->gr_gid) != 0) {
				/* non-fatal: perms stay root-only */
			}
		}
		qm_elogf = fdopen(fd, "a");
		if (qm_elogf == NULL) {
			close(fd);
			return;
		}
	}

	fprintf(qm_elogf, "%llu: ", (unsigned long long)time(NULL));
	va_start(ap, fmt);
	vfprintf(qm_elogf, fmt, ap);
	va_end(ap);
	fputc('\n', qm_elogf);
	fflush(qm_elogf);
}

/* Download the whole plan into PKGDIR up front with a bounded pool of
 * `jobs` forked workers, so the network isn't twiddling its thumbs one
 * package at a time.  Each worker only pulls its own gpkg (distinct file,
 * no VDB, no shared state), a botched download just gets refetched by
 * the serial pkg_fetch afterwards.  Workers open their own trees so they
 * never trample the parent's tree fds across the fork. */
static void
qm_prefetch(array *merge, int jobs)
{
	size_t i;
	char  *cpvp;
	int    running = 0;

	if (jobs < 2 || array_cnt(merge) < 2)
		return;  /* nothing to parallelize */

	if (!quiet)
		printf(">>> Prefetching %zu packages (%d parallel jobs)\n",
				array_cnt(merge), jobs);
	fflush(stdout);
	fflush(stderr);

	/* Parse the binpkg index ONCE here so every forked worker inherits it
	 * copy-on-write, instead of each re-opening and re-parsing the whole
	 * 15MB / thousands-of-pkgs Packages index just to find its one entry.
	 * On slow storage (e.g. a container overlayfs) that redundant re-parse,
	 * not the checksum hash, is what made each package take many seconds.
	 * The parsed tree closed its Packages fd during the parse and keeps
	 * only a directory fd, which is safe to share across fork. */
	if (array_cnt(merge) > 0) {
		char     *first = array_get(merge, 0);
		char      ex[520];
		atom_ctx *wa;

		snprintf(ex, sizeof(ex), "=%s", first);
		wa = atom_explode(ex);
		if (wa != NULL) {
			size_t r;
			size_t rcnt = qm_bintree_cnt();

			/* touch every repo tree so each index parses in the
			 * parent, not once per forked worker */
			for (r = 0; r < rcnt; r++) {
				tree_ctx *bt = qm_bintree(r);

				if (bt != NULL) {
					array *t = tree_match_atom(bt, wa,
							TREE_MATCH_SORT | TREE_MATCH_VIRTUAL |
							TREE_MATCH_ACCT);
					array_free(t);
				}
			}
			atom_implode(wa);
		}
	}

	array_for_each(merge, i, cpvp) {
		pid_t pid;

		/* throttle to `jobs` concurrent downloads */
		while (running >= jobs) {
			if (waitpid(-1, NULL, 0) > 0)
				running--;
			else
				break;
		}

		/* emerge-style per-package progress so a big plan does not look
		 * hung during the (silent, parallel) downloads; -q suppresses it.
		 * The (N of M) counter is carried into pkg_download via these
		 * globals (inherited across fork) so the line prints ONLY when a
		 * file is actually fetched, a repeat -f that skips cached, valid
		 * binpkgs must not scroll 500 spurious "Fetching" lines. */
		qm_dl_n     = i + 1;
		qm_dl_total = array_cnt(merge);

		pid = fork();
		if (pid == 0) {
			/* child: inherit the parent's already-parsed binpkg index; it
			 * is an in-memory COW lookup only, no shared Packages fd, that
			 * was closed at parse time.  Drop the vdb tree; the download
			 * path never needs it. */
			atom_ctx     *ca;
			tree_pkg_ctx *bp;
			char          ex[520];

			_qmerge_vdb_tree    = NULL;
			snprintf(ex, sizeof(ex), "=%s", cpvp);
			ca = atom_explode(ex);
			if (ca != NULL) {
				bp = best_version(ca, BV_BINPKG);
				if (bp != NULL)
					pkg_download(bp);
			}
			_exit(0);
		}
		if (pid > 0)
			running++;
		/* on fork failure just continue, the serial merge fetches it */
	}

	while (running > 0) {
		if (waitpid(-1, NULL, 0) > 0)
			running--;
		else
			break;
	}

	qm_dl_n = qm_dl_total = 0;   /* serial pkg_fetch prints uncounted */
}

/* a cat/pn:slot whose subslot the plan changes, and what it changes to */
struct qm_edge {
	char *consumer;    /* "cat/pf" of the pkg holding the dep (for messages) */
	char *atomstr;     /* the atom, re-exploded when resolving (positive form) */
	char *cusestr;     /* consumer USE flags, for parent-conditional use-deps */
	int   is_blocker;  /* 1 = ! / !! blocker edge, 0 = slot-satisfaction edge */
	int   hard;        /* blocker only: 1 = !! (hard), 0 = ! (soft) */
	int   slotless;    /* 1 = slotless version edge (1c), matched across slots */
	char *consumer_cpslot; /* "cat/pn:slot" of the consumer, Layer 2 upgrade target */
};

struct qm_scctx {
	set   *planned;      /* "cat/pn:slot" being (re)installed by the plan */
	set   *planned_cpn;  /* "cat/pn" the plan touches (any slot), for 1c */
	array *edges;        /* struct qm_edge *, consumer edges to check */
	set   *fixable;      /* nullable: Layer 2 collects stranded consumers to upgrade */
	hash_t *fix_edges;   /* nullable: consumer -> set of broken atomstr */
	int    conflicts;
	int    printed;
};

/* a surviving/planned pkg needs an atom the end-state no longer satisfies and
 * we can't install it from a binpkg, shared reporter, caps the noise */
static void
qm_report_conflict(struct qm_scctx *sc, const char *consumer,
				   const char *atomstr, const char *consumer_cpslot)
{
	sc->conflicts++;
	/* Layer 2: a slot/slotless strand is fixable by upgrading the consumer */
	if (sc->fixable != NULL) {
		if (consumer_cpslot != NULL)
			add_set(consumer_cpslot, sc->fixable);
		if (sc->fix_edges != NULL && atomstr != NULL) {
			const char *ck = consumer_cpslot != NULL ?
					consumer_cpslot : consumer;
			set        *es = hash_get(sc->fix_edges, ck);

			if (es == NULL) {
				es = create_set();
				hash_add(sc->fix_edges, ck, es, NULL);
			}
			add_set_unique(atomstr, es, NULL);
		}
		return;   /* collecting for the cascade, stay quiet */
	}
	if (sc->printed < 12) {
		warn("dep conflict: %s needs %s, but the plan installs a version "
			 "that no longer satisfies it -- can't install it from a binpkg",
			 consumer, atomstr);
		sc->printed++;
	} else if (sc->printed == 12) {
		warn("... and more conflicts");
		sc->printed++;
	}
}

/* is this cat/PF currently installed in the VDB? */
static bool
qm_cpv_installed(const char *cpv)
{
	char          ex[520];
	atom_ctx     *a;
	tree_pkg_ctx *ip;
	bool          ok;

	snprintf(ex, sizeof(ex), "=%s", cpv);
	a = atom_explode(ex);
	if (a == NULL)
		return false;
	ip = best_version(a, BV_INSTALLED);
	ok = ip != NULL;
	atom_implode(a);
	return ok;
}

/* a blocker (! / !!) is violated in the end-state: `who` blocks `blocked`.
 * default is to refuse rather than auto-unmerge something the user didn't
 * ask to drop.  QMERGE_BLOCKERS opts into portage-style soft-block
 * resolution: when the plan (a fresh/planned pkg) SOFT-blocks an already
 * INSTALLED pkg, collect that installed pkg for a safe unmerge before the
 * merge, and treat it as resolved (not a conflict).  Hard blockers (!!),
 * and blocks against not-yet-installed plan members, still refuse. */
static void
qm_report_blocker(struct qm_scctx *sc, const char *who, const char *blocked,
				  int hard)
{
	if (qmerge_blockers && !hard && sc->fixable == NULL &&
			qm_cpv_installed(blocked)) {
		if (qm_soft_unmerge == NULL)
			qm_soft_unmerge = create_set();
		add_set(blocked, qm_soft_unmerge);
		return;   /* resolved by auto-unmerge, not counted as a conflict */
	}
	sc->conflicts++;
	if (sc->fixable != NULL)
		return;   /* cascade collection pass, blockers aren't fixable, stay quiet */
	if (sc->printed < 12) {
		warn("%sblocker: %s blocks %s -- refusing (unmerge it yourself, set "
			 "QMERGE_BLOCKERS to auto-unmerge soft blocks, or "
			 "QMERGE_IGNORE_SLOT_CONFLICTS to override)",
			 hard ? "hard " : "", who, blocked);
		sc->printed++;
	} else if (sc->printed == 12) {
		warn("... and more conflicts");
		sc->printed++;
	}
}

/* does the plan install a package (other than exclude_cpv) that the positive
 * atom `pos` matches?  fills `hit` with the offending cpv.  best_version here
 * is safe, callers run it outside the vdb walk. */
static bool
qm_plan_has_match(array *merge, atom_ctx *pos, set *use,
				  const char *exclude_cpv, char *hit, size_t hitsz)
{
	size_t  i;
	char   *cpvp;

	array_for_each(merge, i, cpvp) {
		char          ex[520];
		atom_ctx     *ca;
		tree_pkg_ctx *c;
		bool          ok;

		if (exclude_cpv != NULL && strcmp(cpvp, exclude_cpv) == 0)
			continue;
		snprintf(ex, sizeof(ex), "=%s", cpvp);
		ca = atom_explode(ex);
		if (ca == NULL)
			continue;
		c  = best_version(ca, BV_BINPKG);
		ok = (c != NULL && atom_satisfied_by(pos, c, use));
		atom_implode(ca);
		if (ok) {
			if (hit != NULL)
				snprintf(hit, hitsz, "%s", cpvp);
			return true;
		}
	}
	return false;
}

/* is the plan's package for cpv a FRESH install (its slot holds nothing yet)?
 * used to fire a blocker only when the plan actually creates the co-install --
 * a pre-existing installed/installed block (qmerge used to ignore blockers, so
 * they can exist) must not refuse a plain reinstall. */
static bool
qm_is_fresh_install(const char *cpv)
{
	char          ex[520];
	char          cpslot[512];
	atom_ctx     *a;
	atom_ctx     *sa;
	atom_ctx     *ba;
	tree_pkg_ctx *bpkg;
	bool          fresh;

	snprintf(ex, sizeof(ex), "=%s", cpv);
	a = atom_explode(ex);
	if (a == NULL)
		return false;
	bpkg = best_version(a, BV_BINPKG);
	if (bpkg == NULL) { atom_implode(a); return false; }
	ba = tree_pkg_atom(bpkg, true);
	snprintf(cpslot, sizeof(cpslot), "%s/%s:%s",
			ba->CATEGORY ? : "", ba->PN ? : "", ba->SLOT ? : "");
	atom_implode(a);

	sa = atom_explode(cpslot);
	fresh = (sa != NULL && best_version(sa, BV_INSTALLED) == NULL);
	if (sa != NULL)
		atom_implode(sa);
	return fresh;
}

/* for a slotless dep (1c): does an installed version of pos's cat/pn, in a
 * slot the plan does NOT replace, still satisfy pos?  A slotless atom can be
 * met by any slot, so we enumerate every installed version across slots and
 * keep the survivors.  Safe outside the vdb walk (tree_match re-queries). */
static bool
qm_surviving_installed_satisfies(atom_ctx *pos, set *planned, set *use)
{
	char          cpn[512];
	atom_ctx     *ca;
	array        *all;
	size_t        n;
	tree_pkg_ctx *m;
	bool          ok = false;

	if (pos->CATEGORY == NULL || pos->PN == NULL || _qmerge_vdb_tree == NULL)
		return false;
	snprintf(cpn, sizeof(cpn), "%s/%s", pos->CATEGORY, pos->PN);
	ca = atom_explode(cpn);
	if (ca == NULL)
		return false;
	all = tree_match_atom(_qmerge_vdb_tree, ca, TREE_MATCH_DEFAULT);
	if (all != NULL) {
		array_for_each(all, n, m) {
			atom_ctx *ma = tree_pkg_atom(m, true);
			char      cps[512];

			snprintf(cps, sizeof(cps), "%s/%s:%s",
					ma->CATEGORY ? : "", ma->PN ? : "", ma->SLOT ? : "");
			if (contains_set(cps, planned) != NULL)
				continue;   /* this slot is being replaced by the plan */
			if (atom_satisfied_by(pos, m, use)) {
				ok = true;
				break;
			}
		}
		array_free(all);
	}
	atom_implode(ca);
	return ok;
}

/* collect only the UNCONDITIONALLY-required atoms of a dep tree: recurse all-of
 * groups, but skip `|| ( )` any-of groups entirely.  Their alternatives are not
 * individually required, so flattening them into edges invents conflicts (perl
 * virtuals declare `|| ( =perl-5.42* =perl-5.40* ... )`, treating each slot as
 * required fires spurious strands).  Safe under-approx: we may miss a conflict
 * where EVERY alternative fails, but never manufacture one.  Caller must
 * dep_prune_use() first so inactive USE-conditionals are already gone. */
static void
qm_collect_required_atoms(dep_node_t *node, array *out)
{
	if (node == NULL)
		return;
	switch (dep_node_type(node)) {
	case DEP_ATOM: {
		atom_ctx *a = dep_node_atom(node);

		if (a != NULL)
			array_append(out, a);
		break;
	}
	case DEP_ANY:
		break;   /* any-of: not required, skip the whole group */
	default: {
		array      *ch = dep_node_children(node);
		size_t      i;
		dep_node_t *c;

		if (ch != NULL)
			array_for_each(ch, i, c)
				qm_collect_required_atoms(c, out);
		break;
	}
	}
}

/* Sweep 1 phase A: one installed pkg, record every RDEPEND edge that points
 * at a cat/pn:slot the plan is about to change, so phase B can resolve it
 * OUTSIDE the vdb walk (best_version here would re-enter the tree we're
 * iterating and invalidate ctxs).  RDEPEND only: a DEPEND-only := is already
 * baked into a built binpkg. */
static int
qm_edge_collect_cb(tree_pkg_ctx *pkg, void *priv)
{
	struct qm_scctx *sc  = priv;
	atom_ctx        *pa  = tree_pkg_atom(pkg, true);
	char             key[512];
	char            *d;
	char            *usestr;
	dep_node_t      *tree;
	array           *atoms;
	size_t           i;
	atom_ctx        *A;

	/* a pkg the plan itself (re)installs is handled by the intra-plan sweep */
	snprintf(key, sizeof(key), "%s/%s:%s",
			pa->CATEGORY ? : "", pa->PN ? : "", pa->SLOT ? : "");
	if (contains_set(key, sc->planned) != NULL)
		return 0;

	d = tree_pkg_meta(pkg, Q_RDEPEND);
	if (d == NULL || *d == '\0')
		return 0;
	tree = dep_grow_tree(d);
	if (tree == NULL)
		return 0;
	usestr = tree_pkg_meta(pkg, Q_USE);   /* borrowed; copied per edge below */
	{
		set *puse = qm_flags_to_set(usestr ? : "");

		dep_prune_use(tree, puse);   /* drop inactive USE-conditional deps */
		free_set(puse);
	}
	atoms = array_new();
	qm_collect_required_atoms(tree, atoms);   /* skips || ( ) any-of groups */
	array_for_each(atoms, i, A) {
		char            cpslot[512];
		struct qm_edge *e;

		/* blocker (! / !!): record the positive form, phase B checks it
		 * against the plan.  ^ antislot deferred. */
		if (A->blocker == ATOM_BL_BLOCK || A->blocker == ATOM_BL_BLOCK_HARD) {
			atom_blocker save = A->blocker;

			A->blocker = ATOM_BL_NONE;
			e = xmalloc(sizeof(*e));
			e->consumer   = xstrdup(atom_format("%[CAT]%[PF]", pa));
			e->atomstr    = xstrdup(atom_to_string(A));
			e->cusestr    = xstrdup(usestr ? : "");
			e->is_blocker = 1;
			e->hard       = (save == ATOM_BL_BLOCK_HARD);
			e->slotless   = 0;
			e->consumer_cpslot = xstrdup(key);
			A->blocker    = save;
			array_append(sc->edges, e);
			continue;
		}
		if (A->blocker != ATOM_BL_NONE)   /* ^ antislot etc: skip */
			continue;
		/* slotless version edge (1c): a dep with no :slot can be met by any
		 * slot, so record it if the plan touches this cat/pn at all. */
		if (A->SLOT == NULL) {
			char cpn[512];

			if (A->CATEGORY == NULL || A->PN == NULL)
				continue;
			snprintf(cpn, sizeof(cpn), "%s/%s", A->CATEGORY, A->PN);
			if (contains_set(cpn, sc->planned_cpn) == NULL)
				continue;
			e = xmalloc(sizeof(*e));
			e->consumer   = xstrdup(atom_format("%[CAT]%[PF]", pa));
			e->atomstr    = xstrdup(atom_to_string(A));
			e->cusestr    = xstrdup(usestr ? : "");
			e->is_blocker = 0;
			e->hard       = 0;
			e->slotless   = 1;
			e->consumer_cpslot = xstrdup(key);
			array_append(sc->edges, e);
			continue;
		}
		snprintf(cpslot, sizeof(cpslot), "%s/%s:%s",
				A->CATEGORY ? : "", A->PN ? : "", A->SLOT);
		if (contains_set(cpslot, sc->planned) == NULL)
			continue;                     /* plan doesn't touch this provider */

		e = xmalloc(sizeof(*e));
		e->consumer   = xstrdup(atom_format("%[CAT]%[PF]", pa));
		e->atomstr    = xstrdup(atom_to_string(A));
		e->cusestr    = xstrdup(usestr ? : "");
		e->is_blocker = 0;
		e->hard       = 0;
		e->slotless   = 0;
		e->consumer_cpslot = xstrdup(key);
		array_append(sc->edges, e);
	}
	array_free(atoms);   /* atoms are tree-owned; free only the container */
	dep_burn_tree(tree);
	return 0;
}

/* Resolve the complete end-state graph and refuse a plan that would strand a
 * package we can't rebuild from a binpkg.  End-state = (installed pkgs the plan
 * doesn't replace) + (planned binpkgs).  For every RDEPEND edge of every
 * end-state pkg that points at a cat/pn:slot the plan changes, check the
 * planned version still satisfies the full atom (version op, slot, subslot,
 * USE, not just subslot).  For installed consumers we only refuse when the
 * edge worked BEFORE the plan, matching portage's complete-graph
 * "initially-satisfied-now-broken" classification, so a pre-existing breakage
 * never blocks a merge.  Portage backtracks/rebuilds here; we say no.  Returns
 * the number of conflicts (0 = end-state is consistent). */
static int
qm_check_slot_conflicts(array *merge, set *fixable, hash_t *fix_edges)
{
	struct qm_scctx sc;
	size_t          i;
	char           *cpvp;
	struct qm_edge *e;

	set *seen = create_set();   /* cpslot -> cpv, to catch same-slot version dups */

	sc.planned     = create_set();
	sc.planned_cpn = create_set();
	sc.edges       = array_new();
	sc.fixable     = fixable;   /* nullable; Layer 2 collects upgrade targets */
	sc.fix_edges   = fix_edges;
	sc.conflicts   = 0;
	sc.printed     = 0;

	/* which cat/pn:slot (and bare cat/pn, for 1c) the plan (re)installs */
	array_for_each(merge, i, cpvp) {
		char          ex[520];
		char          cpslot[512];
		char          cpn[512];
		const char   *prev;
		atom_ctx     *a;
		tree_pkg_ctx *bpkg;
		atom_ctx     *ba;

		snprintf(ex, sizeof(ex), "=%s", cpvp);
		a = atom_explode(ex);
		if (a == NULL)
			continue;
		bpkg = best_version(a, BV_BINPKG);
		if (bpkg == NULL) { atom_implode(a); continue; }
		ba = tree_pkg_atom(bpkg, true);
		snprintf(cpslot, sizeof(cpslot), "%s/%s:%s",
				ba->CATEGORY ? : "", ba->PN ? : "",
				ba->SLOT ? : "");
		snprintf(cpn, sizeof(cpn), "%s/%s",
				ba->CATEGORY ? : "", ba->PN ? : "");

		/* slot collision: two DIFFERENT versions of the same cat/pn:slot in one
		 * plan = contradictory version requirements the forward walk couldn't
		 * reconcile (portage backtracks; we can't, so refuse, slot-collapse
		 * would otherwise silently drop one and break its consumer).  Not
		 * fixable by upgrading a consumer, so it never lands in `fixable`. */
		prev = get_set(cpslot, seen);
		if (prev != NULL && strcmp(prev, cpvp) != 0) {
			sc.conflicts++;
			if (sc.fixable == NULL && sc.printed < 12) {
				warn("slot collision: the plan installs both %s and %s in the "
					 "same slot (%s) -- contradictory versions, refusing",
					 prev, cpvp, cpslot);
				sc.printed++;
			}
		} else if (prev == NULL) {
			add_set_value(cpslot, (void *)cpvp, NULL, seen);
		}

		add_set(cpslot, sc.planned);
		add_set(cpn, sc.planned_cpn);
		atom_implode(a);
	}

	/* Sweep 1 phase A: collect installed-consumer edges (no best_version) */
	if (_qmerge_vdb_tree != NULL)
		tree_foreach_pkg_fast(_qmerge_vdb_tree, qm_edge_collect_cb, &sc, NULL);

	/* Sweep 1 phase B: now safe to resolve providers.  Refuse only if the
	 * planned version breaks an edge the installed version satisfied. */
	array_for_each(sc.edges, i, e) {
		atom_ctx     *A;
		atom_ctx     *ca;
		char          cpslot[512];
		set          *cuse;
		tree_pkg_ctx *newp;
		tree_pkg_ctx *oldp;

		A = atom_explode(e->atomstr);
		if (A == NULL)
			continue;
		cuse = qm_flags_to_set(e->cusestr);

		/* blocker: an installed pkg blocks something.  Only fire if the PLAN
		 * introduces the blocked pkg, a pre-existing installed/installed
		 * block isn't the plan's doing (initially-satisfied logic). */
		if (e->is_blocker) {
			char hit[520];

			/* fire only if the plan freshly introduces the blocked pkg */
			if (qm_plan_has_match(merge, A, cuse, NULL, hit, sizeof(hit)) &&
				qm_is_fresh_install(hit))
				qm_report_blocker(&sc, e->consumer, hit, e->hard);
			free_set(cuse);
			atom_implode(A);
			continue;
		}

		/* slotless (1c): fire only if it was satisfied before AND nothing in
		 * the end-state (planned, or an installed survivor in any slot) still
		 * satisfies it, i.e. the plan dropped the last matching version. */
		if (e->slotless) {
			tree_pkg_ctx *mbest = best_version(A, BV_INSTALLED);

			if (mbest != NULL && atom_satisfied_by(A, mbest, cuse) &&
				!qm_plan_has_match(merge, A, cuse, NULL, NULL, 0) &&
				!qm_surviving_installed_satisfies(A, sc.planned, cuse))
				qm_report_conflict(&sc, e->consumer, e->atomstr,
						e->consumer_cpslot);
			free_set(cuse);
			atom_implode(A);
			continue;
		}

		snprintf(cpslot, sizeof(cpslot), "%s/%s:%s",
				A->CATEGORY ? : "", A->PN ? : "", A->SLOT ? : "");
		ca = atom_explode(cpslot);
		if (ca == NULL) { free_set(cuse); atom_implode(A); continue; }

		/* newp fully consumed before oldp is fetched (ctx invalidation) */
		newp = best_version(ca, BV_BINPKG);
		if (newp != NULL && !atom_satisfied_by(A, newp, cuse)) {
			oldp = best_version(ca, BV_INSTALLED);
			if (oldp != NULL && atom_satisfied_by(A, oldp, cuse))
				qm_report_conflict(&sc, e->consumer, e->atomstr,
						e->consumer_cpslot);
		}
		free_set(cuse);
		atom_implode(ca);
		atom_implode(A);
	}

	/* Sweep 2: intra-plan edges, a planned consumer's binpkg was built
	 * against a subslot/version the plan may not be installing (multi-binhost
	 * skew).  End-state provider = planned if planned, else installed.  No
	 * initially-satisfied gate: a package's own bindings must hold in the set
	 * it lands in. */
	array_for_each(merge, i, cpvp) {
		char          ex[520];
		atom_ctx     *pca;
		tree_pkg_ctx *pbin;
		char         *pcons;
		char         *prdep;
		char         *puse;
		char         *pcons_cpslot;
		dep_node_t   *tree;
		array        *atoms;
		size_t        j;
		atom_ctx     *A;
		set          *cuse;
		bool          p_fresh;

		snprintf(ex, sizeof(ex), "=%s", cpvp);
		pca = atom_explode(ex);
		if (pca == NULL)
			continue;
		pbin = best_version(pca, BV_BINPKG);
		if (pbin == NULL) { atom_implode(pca); continue; }
		/* B1: snapshot before any further best_version invalidates pbin */
		{
			atom_ctx *pba = tree_pkg_atom(pbin, true);
			char      pcs[512];

			pcons = xstrdup(atom_format("%[CAT]%[PF]", pba));
			snprintf(pcs, sizeof(pcs), "%s/%s:%s",
					pba->CATEGORY ? : "", pba->PN ? : "", pba->SLOT ? : "");
			pcons_cpslot = xstrdup(pcs);
		}
		prdep = xstrdup(tree_pkg_meta(pbin, Q_RDEPEND) ? : "");
		puse  = xstrdup(tree_pkg_meta(pbin, Q_USE)     ? : "");
		atom_implode(pca);
		p_fresh = qm_is_fresh_install(cpvp);   /* for the blocker gate below */

		tree = dep_grow_tree(prdep);
		if (tree != NULL) {
			cuse  = qm_flags_to_set(puse);
			dep_prune_use(tree, cuse);   /* drop inactive USE-conditional deps */
			atoms = array_new();
			qm_collect_required_atoms(tree, atoms);   /* skip || ( ) groups */
			array_for_each(atoms, j, A) {
				char          cpslot[512];
				atom_ctx     *ca;
				tree_pkg_ctx *prov;

				/* blocker from a planned pkg: violated if the end-state (an
				 * installed pkg that survives, or another planned pkg) holds a
				 * match.  A same-slot version being replaced isn't in the
				 * end-state, so a self-block on the old version won't fire. */
				if (A->blocker == ATOM_BL_BLOCK ||
					A->blocker == ATOM_BL_BLOCK_HARD) {
					atom_blocker  save = A->blocker;
					tree_pkg_ctx *m;
					char          hit[520];

					A->blocker = ATOM_BL_NONE;
					/* planned P blocks an installed pkg that survives: the
					 * co-install is new only if P itself is a fresh install
					 * (a reinstall/upgrade already coexisted with it). */
					if (p_fresh) {
						m = best_version(A, BV_INSTALLED);
						if (m != NULL && atom_satisfied_by(A, m, cuse)) {
							atom_ctx *ma = tree_pkg_atom(m, true);
							char      mcps[512];

							snprintf(mcps, sizeof(mcps), "%s/%s:%s",
									ma->CATEGORY ? : "", ma->PN ? : "",
									ma->SLOT ? : "");
							if (contains_set(mcps, sc.planned) == NULL) {
								char mcpv[520];

								snprintf(mcpv, sizeof(mcpv), "%s/%s",
										ma->CATEGORY ? : "", ma->PF ? : "");
								qm_report_blocker(&sc, pcons, mcpv,
										save == ATOM_BL_BLOCK_HARD);
							}
						}
					}
					/* planned P blocks another planned pkg: fire if either is a
					 * fresh install (both pre-installed = pre-existing) */
					if (qm_plan_has_match(merge, A, cuse, cpvp,
										  hit, sizeof(hit)) &&
						(p_fresh || qm_is_fresh_install(hit)))
						qm_report_blocker(&sc, pcons, hit,
								save == ATOM_BL_BLOCK_HARD);
					A->blocker = save;
					continue;
				}
				if (A->blocker != ATOM_BL_NONE)   /* ^ antislot: skip */
					continue;
				/* slotless (1c): a planned pkg's slotless dep must be met by
				 * some end-state version (planned or installed survivor). */
				if (A->SLOT == NULL) {
					char cpn[512];

					if (A->CATEGORY == NULL || A->PN == NULL)
						continue;
					snprintf(cpn, sizeof(cpn), "%s/%s",
							A->CATEGORY, A->PN);
					if (contains_set(cpn, sc.planned_cpn) == NULL)
						continue;   /* plan doesn't touch this cat/pn */
					if (!qm_plan_has_match(merge, A, cuse, NULL, NULL, 0) &&
						!qm_surviving_installed_satisfies(A, sc.planned, cuse))
						qm_report_conflict(&sc, pcons, atom_to_string(A), pcons_cpslot);
					continue;
				}
				snprintf(cpslot, sizeof(cpslot), "%s/%s:%s",
						A->CATEGORY ? : "", A->PN ? : "", A->SLOT);
				ca = atom_explode(cpslot);
				if (ca == NULL)
					continue;
				prov = (contains_set(cpslot, sc.planned) != NULL)
					   ? best_version(ca, BV_BINPKG)
					   : best_version(ca, BV_INSTALLED);
				if (prov != NULL && !atom_satisfied_by(A, prov, cuse))
					qm_report_conflict(&sc, pcons, atom_to_string(A), pcons_cpslot);
				atom_implode(ca);
			}
			array_free(atoms);   /* tree-owned atoms; free only the container */
			free_set(cuse);
			dep_burn_tree(tree);
		}
		free(pcons);
		free(pcons_cpslot);
		free(prdep);
		free(puse);
	}

	array_for_each(sc.edges, i, e) {
		free(e->consumer);
		free(e->atomstr);
		free(e->cusestr);
		free(e->consumer_cpslot);
		free(e);
	}
	array_free(sc.edges);
	free_set(sc.planned);
	free_set(sc.planned_cpn);
	free_set(seen);
	return sc.conflicts;
}

/* Layer 2 (-u): instead of refusing a strand, pull a NEWER binpkg of the
 * stranded consumer (portage would rebuild it; we pull a newer build).  That
 * may strand ITS consumers -> iterate to a fixpoint.  Monotone: each step adds
 * a strictly-newer, not-yet-planned version, so it terminates; the cap is only
 * a backstop.  Blockers and provider-downgrades never land in `fixable`, so
 * they persist and the caller's sweep refuses on them.  Augments plan->merge
 * in place; the loud sweep in the caller reports whatever is left. */
#define QM_MAX_FIXPOINT 64  /* hard safety ceiling over --backtrack */
/* map of cat/pn -> cloned full atom of the provider the plan installs;
 * used to pin-check repair candidates against the planned stack */
static hash_t *
qm_planned_map_build(struct qm_plan *plan)
{
	hash_t *map = hash_new();
	size_t  i;
	char   *cpvp;

	array_for_each(plan->merge, i, cpvp) {
		char          ex[560];
		atom_ctx     *a;
		tree_pkg_ctx *bp;
		char          cpn[512];

		snprintf(ex, sizeof(ex), "=%s", cpvp);
		a = atom_explode(ex);
		if (a == NULL)
			continue;
		bp = best_version(a, BV_BINPKG);
		if (bp != NULL) {
			atom_ctx *fa = tree_pkg_atom(bp, true);

			snprintf(cpn, sizeof(cpn), "%s/%s",
					 fa->CATEGORY ? : "", fa->PN ? : "");
			if (hash_get(map, cpn) == NULL)
				hash_add(map, cpn, atom_clone(fa), NULL);
		}
		atom_implode(a);
	}
	return map;
}

static void
qm_planned_map_free(hash_t *map)
{
	array *vals = hash_values(map);

	array_deepfree(vals, (array_free_cb *)atom_implode);
	hash_free(map);
}

/* do the candidate's baked subslot pins agree with the planned stack?
 * Only atoms with an explicit SUBSLOT whose provider the plan touches
 * are enforced, the strand class being repaired */
static bool
qm_cand_pins_ok(tree_pkg_ctx *cand, hash_t *pinmap)
{
	char       *rdep = tree_pkg_meta(cand, Q_RDEPEND);
	set        *cuse;
	dep_node_t *t;
	array      *flat;
	size_t      i;
	atom_ctx   *A;
	bool        ok = true;

	if (rdep == NULL || *rdep == '\0')
		return true;

	cuse = qm_flags_to_set(tree_pkg_meta(cand, Q_USE));
	t    = dep_grow_tree(rdep);
	if (t == NULL) {
		free_set(cuse);
		return true;
	}
	dep_prune_use(t, cuse);
	/* dep_flatten_tree yields atom pointers, not nodes */
	flat = dep_flatten_tree(t);
	array_for_each(flat, i, A) {
		char      cpn[512];
		atom_ctx *planned;

		if (A == NULL || A->SUBSLOT == NULL ||
				A->blocker != ATOM_BL_NONE ||
				A->CATEGORY == NULL || A->PN == NULL)
			continue;
		snprintf(cpn, sizeof(cpn), "%s/%s", A->CATEGORY, A->PN);
		planned = hash_get(pinmap, cpn);
		if (planned == NULL)
			continue;
		if (atom_compare_flg(planned, A,
				ATOM_COMP_DEFAULT | ATOM_COMP_NOREPO) != EQUAL) {
			ok = false;
			break;
		}
	}
	array_free(flat);
	dep_burn_tree(t);
	free_set(cuse);
	return ok;
}

/* find the best repair candidate for a stranded consumer: newest
 * visible binpkg ACROSS repos (any build id, binpkg-multi-instance
 * rebuilds of the same version count, cf. emerge --rebuilt-binaries)
 * whose baked pins agree with the planned stack */
static tree_pkg_ctx *
qm_repair_pick(atom_ctx *ca, hash_t *pinmap, ssize_t *repo_out)
{
	size_t        rcnt = qm_bintree_cnt();
	size_t        ri;
	tree_pkg_ctx *best  = NULL;
	ssize_t       brepo = -1;

	for (ri = 0; ri < rcnt; ri++) {
		tree_ctx     *bt = qm_bintree(ri);
		array        *t;
		size_t        n;
		tree_pkg_ctx *cand;

		if (bt == NULL)
			continue;
		t = tree_match_atom(bt, ca,
				TREE_MATCH_SORT | TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);
		array_for_each(t, n, cand) {
			atom_ctx *pa = tree_pkg_atom(cand, true);

			if (binpkg_masked(pa))
				continue;
			if (!binpkg_keywords_ok(cand, pa, true))
				continue;
			if (!binpkg_license_ok(cand, pa, true))
				continue;
			if (binpkg_excluded(cand, pa, true))
				continue;
			if (!qm_cand_pins_ok(cand, pinmap))
				continue;
			if (best == NULL ||
					atom_compare(tree_pkg_atom(cand, true),
								 tree_pkg_atom(best, true)) == NEWER) {
				best  = cand;
				brepo = (ssize_t)ri;
			}
			break;   /* highest-first within repo: first passing = best */
		}
		array_free(t);
	}
	*repo_out = brepo;
	return best;
}

/* drop every plan entry of cat/pn (hold-back: keep the installed
 * version instead of the planned upgrade) */
static int
qm_plan_drop(struct qm_plan *plan, const char *cpn)
{
	size_t i;
	int    dropped = 0;

	for (i = array_cnt(plan->merge); i-- > 0; ) {
		char     *cpvp = array_get(plan->merge, i);
		char      ex[560];
		atom_ctx *a;
		bool      match = false;

		snprintf(ex, sizeof(ex), "=%s", cpvp);
		a = atom_explode(ex);
		if (a != NULL) {
			char ecpn[512];

			snprintf(ecpn, sizeof(ecpn), "%s/%s",
					 a->CATEGORY ? : "", a->PN ? : "");
			match = strcmp(ecpn, cpn) == 0;
			atom_implode(a);
		}
		if (match) {
			bool ign;

			(void)del_set(cpvp, plan->in_merge, &ign);
			/* array_delete with a NULL callback frees the element */
			array_delete(plan->merge, i, NULL);
			dropped++;
		}
	}
	return dropped;
}

static void
qm_layer2_resolve(struct qm_plan *plan, set *todo)
{
	int  iter;
	int  budget = qm_backtrack;
	int  used   = 0;
	set *held   = create_set();   /* cat/pn already held back */

	if (budget < 0 || budget > QM_MAX_FIXPOINT)
		budget = QM_MAX_FIXPOINT;

	for (iter = 0; iter < budget; iter++) {
		set     *fixable   = create_set();
		hash_t  *fix_edges = hash_new();
		hash_t  *pinmap;
		bool     progress  = false;
		size_t   before;
		array   *keys;
		char    *cpslot;
		size_t   k;

		/* quiet sweep (fixable != NULL): collect stranded consumers */
		(void)qm_check_slot_conflicts(plan->merge, fixable, fix_edges);
		if (cnt_set(fixable) == 0) {
			array *ev = hash_values(fix_edges);

			array_deepfree(ev, (array_free_cb *)set_free);
			hash_free(fix_edges);
			free_set(fixable);
			break;
		}
		pinmap = qm_planned_map_build(plan);

		before = array_cnt(plan->merge);
		keys   = set_keys(fixable);
		array_for_each(keys, k, cpslot) {
			atom_ctx     *ca = atom_explode(cpslot);
			tree_pkg_ctx *newc;
			atom_ctx     *na;
			ssize_t       nrepo = -1;
			char          newcpv[520];
			char          exact[560];
			atom_ctx     *ea;
			bool          in_plan = false;

			if (ca == NULL)
				continue;
			/* strategy A: a rebuilt consumer whose baked pins agree
			 * with the planned stack, newest across repos, ANY build
			 * id (a same-version multi-instance rebuild is the normal
			 * fix when only the provider subslot moved) */
			newc = qm_repair_pick(ca, pinmap, &nrepo);
			if (newc != NULL) {
				na = tree_pkg_atom(newc, false);
				snprintf(newcpv, sizeof(newcpv), "%s/%s",
						 na->CATEGORY ? : "", na->PF ? : "");
				if (contains_set(newcpv, plan->in_merge) != NULL)
					in_plan = true;
				if (!in_plan && nrepo >= 0 && qm_nbinrepos > 1) {
					char pinned[560];

					snprintf(pinned, sizeof(pinned), "%s::@%s",
							 newcpv, qm_binrepos[nrepo].name);
					if (contains_set(pinned, plan->in_merge) != NULL)
						in_plan = true;
				}
			}
			if (newc != NULL && !in_plan) {
				/* pull the exact rebuild, pinned to its serving repo:
				 * its dep subtree then resolves with that repo's
				 * affinity, keeping the repaired cohort consistent */
				if (nrepo > 0 && qm_nbinrepos > 0)
					snprintf(exact, sizeof(exact), "=%s::@%s",
							 newcpv, qm_binrepos[nrepo].name);
				else
					snprintf(exact, sizeof(exact), "=%s", newcpv);
				ea = atom_explode(exact);
				if (ea != NULL) {
					char msg[560];
					char key[560];

					qm_resolve(ea, NULL, plan, 0);
					atom_implode(ea);
					progress = true;
					snprintf(msg, sizeof(msg),
							 "pulled to repair a dependency conflict "
							 "(backtrack round %d)", iter + 1);
					snprintf(key, sizeof(key), "=%s%s%s%s", newcpv,
							 nrepo >= 0 && qm_nbinrepos > 1 ? " [" : "",
							 nrepo >= 0 && qm_nbinrepos > 1 ?
								 qm_binrepos[nrepo].name : "",
							 nrepo >= 0 && qm_nbinrepos > 1 ? "]" : "");
					qm_notice(key, msg);
				}
			} else if (newc == NULL) {
				/* strategy B: no rebuilt consumer exists anywhere --
				 * hold the breaking provider back at its installed
				 * version, unless the user explicitly asked for it */
				set   *es = hash_get(fix_edges, cpslot);
				array *ek = es != NULL ? set_keys(es) : NULL;
				size_t ei;
				char  *astr;

				if (ek != NULL)
				array_for_each(ek, ei, astr) {
					atom_ctx *A = atom_explode(astr);
					char      pcpn[512];

					if (A == NULL || A->CATEGORY == NULL ||
							A->PN == NULL) {
						if (A != NULL)
							atom_implode(A);
						continue;
					}
					snprintf(pcpn, sizeof(pcpn), "%s/%s",
							 A->CATEGORY, A->PN);
					if (contains_set(pcpn, held) == NULL &&
							!qm_atom_is_target(A, todo) &&
							qm_plan_drop(plan, pcpn) > 0) {
						char msg[560];
						char key[560];

						add_set(pcpn, held);
						progress = true;
						snprintf(key, sizeof(key), "%s", pcpn);
						snprintf(msg, sizeof(msg),
								 "held back at the installed version: "
								 "installed consumers pin it and no "
								 "rebuilt binpkgs exist (backtrack "
								 "round %d)", iter + 1);
						qm_notice(key, msg);
					}
					atom_implode(A);
				}
				if (ek != NULL)
					array_free(ek);
			}
			atom_implode(ca);
		}
		array_free(keys);
		free_set(fixable);
		{
			array *ev = hash_values(fix_edges);

			array_deepfree(ev, (array_free_cb *)set_free);
			hash_free(fix_edges);
		}
		qm_planned_map_free(pinmap);

		if (!progress && array_cnt(plan->merge) == before)
			break;   /* stuck: remaining conflicts are genuine */
		used = iter + 1;
	}

	free_set(held);
	/* plan-output companion line: the pretend/dry-run path runs with
	 * quiet=1 yet still prints the plan, so no quiet gate here */
	if (used > 0)
		printf(">>> Backtracked %d round(s) to repair dependency "
			   "conflicts\n", used);
}

/* resolve the requested atoms into a dependency-ordered plan, then
 * fetch+merge each package deps-first.  pretend/fetch modes flow through
 * pkg_fetch (which prints in pretend and skips merge for --fetchonly). */
static int
qm_resolve_and_merge(set *todo)
{
	struct qm_plan plan;
	array         *keys;
	char          *k;
	char          *cpvp;
	size_t         i;

	plan.merge    = array_new();
	plan.in_merge = create_set();
	plan.examined = create_set();

	/* fresh soft-block auto-unmerge collection for this run */
	if (qm_soft_unmerge != NULL) {
		free_set(qm_soft_unmerge);
		qm_soft_unmerge = NULL;
	}

	keys = set_keys(todo);
	array_for_each(keys, i, k) {
		atom_ctx *a = atom_explode(k);
		char     *picked_cat = NULL;

		if (a == NULL)
			continue;
		/* qualify a bare package name the way portage does; the picked
		 * category is our own allocation, atom_implode never frees it */
		if (a->CATEGORY == NULL && a->PN != NULL) {
			bool ambiguous = false;

			picked_cat = qm_pick_category(a->PN, &ambiguous);
			if (picked_cat != NULL)
				a->CATEGORY = picked_cat;
			else if (ambiguous)
				warn("ambiguous package name '%s', please qualify "
					 "with a category", a->PN);
		}
		qm_resolve(a, NULL, &plan, 0);
		atom_implode(a);
		free(picked_cat);
	}
	array_free(keys);

	/* Layer 2 (backtrack): resolve strands by pulling newer consumer
	 * binpkgs, augmenting plan.merge in place; the sweep below then
	 * reports (and refuses on) whatever couldn't be resolved.  Runs
	 * for every resolve like portage's backtrack_depgraph; --backtrack
	 * 0 restores single-shot refuse-on-conflict behavior. */
	if (qm_backtrack != 0 && array_cnt(plan.merge) > 0)
		qm_layer2_resolve(&plan, todo);

	int rc = EXIT_SUCCESS;

	if (array_cnt(plan.merge) == 0) {
		/* nothing resolved, the request couldn't be satisfied (no candidate
		 * binpkg, or the index/download failed).  Signal failure so the
		 * interactive caller skips the "OK to merge" prompt: there are no
		 * packages to offer.  USE-gate rejects explain a respect-use refusal
		 * that would otherwise read as a bare cannot-satisfy. */
		qm_print_use_rejects();
		warn("nothing to merge (no candidates could be satisfied)");
		array_deepfree(plan.merge, free);
		free_set(plan.in_merge);
		free_set(plan.examined);
		return EXIT_FAILURE;
	} else if (pretend) {
		/* pretend: show the resolved plan (deps first), install status
		 * relative to what is installed, without fetching or merging */
		size_t             n_new = 0, n_up = 0, n_re = 0, n_down = 0;
		unsigned long long dlbytes = 0;

		printf("These are the packages that would be merged, "
			   "in order:\n\n");
		array_for_each(plan.merge, i, cpvp) {
			atom_ctx     *a;
			atom_ctx     *ba;
			tree_pkg_ctx *inst;
			tree_pkg_ctx *bpkg;
			char          exact[520];
			const char   *st = "N";

			char bidbuf[32] = "";

			snprintf(exact, sizeof(exact), "=%s", cpvp);
			a = atom_explode(exact);
			if (a == NULL)
				continue;
			bpkg = best_version(a, BV_BINPKG);
			ba   = a;
			if (bpkg != NULL) {
				/* full atom carries SLOT from metadata, so the status
				 * reflects slot occupancy, matching emerge and the
				 * slot-collapse install path */
				atom_ctx *bat = tree_pkg_atom(bpkg, true);

				st = qm_slot_status(bat, NULL);
				/* cosmetic: show the binpkg-multi-instance build id like
				 * emerge's -N.  Purely display, the [R]/[U] decision above
				 * is version-only and ignores the build id. */
				if (bat->BUILDID > 0)
					snprintf(bidbuf, sizeof(bidbuf), "-%u", bat->BUILDID);
			}
			(void)ba;
			(void)inst;
			/* colored via the global rule: tty auto-color, disabled by
			 * -C/--nocolor/NOCOLOR/NO_COLOR/QMERGE_NOCOLOR, forced by
			 * --color (the color globals are empty strings when nocolor
			 * wins).  Binary merges use portage's PKG_BINARY_MERGE
			 * family (purple/magenta, cf. emerge -K), NOT green --
			 * green means from-source in emerge terms. */
			{
				const char *stc = st[0] == 'N' ? GREEN :
								  st[0] == 'R' ? YELLOW :
								  st[0] == 'U' ? BLUE :
								  st[0] == 'D' ? DKBLUE : RED;
				/* explicit targets bold like emerge's world entries
				 * (PKG_BINARY_MERGE_WORLD = fuchsia = magenta+bold),
				 * dependencies stay plain magenta */
				bool        tgt = qm_atom_is_target(a, todo);
				const char *pc  = *NORM == '\0' ? "" :
								  tgt ? "\033[35;01m" : MAGENTA;

				switch (st[0]) {
				case 'N': n_new++;  break;
				case 'U': n_up++;   break;
				case 'R': n_re++;   break;
				case 'D': n_down++; break;
			}
			if (bpkg != NULL &&
					faccessat(tree_pkg_get_portroot_fd(bpkg),
							  tree_pkg_get_path(bpkg), R_OK, 0) != 0) {
				char *szs = tree_pkg_meta(bpkg, Q_SIZE);

				if (szs != NULL && *szs != '\0')
					dlbytes += strtoull(szs, NULL, 10);
			}
			printf("[%sbinary%s %s%s%s", pc, NORM, stc, st, NORM);
				if (bpkg != NULL) {
					const char *km = qm_keyword_marker(bpkg);

					if (km[0] != '\0')
						printf(" %s%s%s",
							   *NORM == '\0' ? "" : "\033[33;01m",
							   km, NORM);
				}
				/* plan entries may carry a ::binrepo pin; the [repo]
				 * tag already shows it, keep the name clean */
				{
					const char *rsep = strstr(cpvp, "::");
					int         cl   = rsep != NULL ?
							(int)(rsep - cpvp) : (int)strlen(cpvp);

					printf("] %s%.*s%s%s", pc, cl, cpvp, bidbuf, NORM);
				}

				/* SLOT/SUBSLOT and source-repo provenance, like emerge's
				 * cat/pf-BID:slot/sub::repo.  Portage colors the whole atom
				 * (name+slot+repo) as one run via pkgprint, so reuse the
				 * package color pc rather than highlighting slot/repo apart. */
				if (bpkg != NULL) {
					atom_ctx *sat  = tree_pkg_atom(bpkg, true);
					char     *repo = tree_pkg_meta(bpkg, Q_repository);

					if (sat->SLOT != NULL) {
						printf("%s:%s", pc, sat->SLOT);
						if (sat->SUBSLOT != NULL &&
								strcmp(sat->SLOT, sat->SUBSLOT) != 0)
							printf("/%s", sat->SUBSLOT);
						printf("%s", NORM);
					}
					if (repo != NULL && *repo != '\0')
						printf("%s::%s%s", pc, repo, NORM);
				}

				if (bpkg != NULL && qm_nbinrepos > 1) {
					const char *rn = qm_repo_name_of_pkg(bpkg);

					if (rn != NULL)
						printf(" %s[%s]%s",
							   qm_repo_tag_color_b(tgt), rn, NORM);
				}
			}
			printf("\n");
			/* a foreign-repo pkg (or, with -N, any USE-changed rebuild)
			 * replacing an installed one: surface how its built USE
			 * differs from what is on the box */
			if (bpkg != NULL && (newuse || qm_repoidx_of_pkg(bpkg) > 0)) {
				atom_ctx *bat = tree_pkg_atom(bpkg, true);
				char      cpn[_Q_PATH_MAX];
				atom_ctx *ca;

				snprintf(cpn, sizeof(cpn), "%s/%s",
						 bat->CATEGORY, bat->PN);
				ca = atom_explode(cpn);
				if (ca != NULL) {
					tree_pkg_ctx *ipkg = best_version(ca, BV_VDB);

					if (ipkg != NULL) {
						char *drift = qm_use_drift(bpkg, ipkg);

						if (drift != NULL) {
							printf("           %sUSE delta vs installed:%s "
								   "%s\n", YELLOW, NORM, drift);
							free(drift);
						}
					}
					atom_implode(ca);
				}
			}
			atom_implode(a);
		}
		{
			char   parts[160] = "";
			size_t po = 0;

			if (n_up > 0)
				po += (size_t)snprintf(parts + po, sizeof(parts) - po,
						"%s%zu upgrade%s", po ? ", " : "",
						n_up, n_up == 1 ? "" : "s");
			if (n_new > 0)
				po += (size_t)snprintf(parts + po, sizeof(parts) - po,
						"%s%zu new", po ? ", " : "", n_new);
			if (n_re > 0)
				po += (size_t)snprintf(parts + po, sizeof(parts) - po,
						"%s%zu reinstall%s", po ? ", " : "",
						n_re, n_re == 1 ? "" : "s");
			if (n_down > 0)
				po += (size_t)snprintf(parts + po, sizeof(parts) - po,
						"%s%zu downgrade%s", po ? ", " : "",
						n_down, n_down == 1 ? "" : "s");

			printf("\nTotal: %zu package%s%s%s%s, "
				   "Size of downloads: %llu KiB\n",
				   array_cnt(plan.merge),
				   array_cnt(plan.merge) == 1 ? "" : "s",
				   po ? " (" : "", parts, po ? ")" : "",
				   dlbytes / 1024);
		}
		qm_print_use_rejects();
		/* surface subslot conflicts in the plan too, like emerge does; a
		 * contradictory plan is a failure even in pretend, and (crucially)
		 * makes the interactive dry-run return non-zero so the caller skips
		 * the "OK to merge" prompt instead of offering a plan we refuse. */
		if (qm_check_slot_conflicts(plan.merge, NULL, NULL) > 0 &&
			getenv("QMERGE_IGNORE_SLOT_CONFLICTS") == NULL)
			rc = EXIT_FAILURE;
		if (qmerge_blockers && qm_soft_unmerge != NULL &&
				cnt_set(qm_soft_unmerge) > 0) {
			array  *bk = set_keys(qm_soft_unmerge);
			size_t  bn;
			char   *bp;

			printf("\nSoft-blocked, would be auto-unmerged first "
				   "(QMERGE_BLOCKERS):\n");
			array_for_each(bk, bn, bp)
				printf("  [%suninstall%s] %s\n", RED, NORM, bp);
			array_free(bk);
		}
	} else if (qm_check_slot_conflicts(plan.merge, NULL, NULL) > 0 &&
			   getenv("QMERGE_IGNORE_SLOT_CONFLICTS") == NULL) {
		/* the plan would strand installed packages we can't rebuild from a
		 * binpkg; bail instead of half-migrating and breaking the system */
		warn("refusing to merge: the plan would break installed packages "
			 "(subslot conflict above). Rebuild them from source with "
			 "emerge, or set QMERGE_IGNORE_SLOT_CONFLICTS=1 to force it.");
		rc = EXIT_FAILURE;
	} else {
		qm_print_use_rejects();
		/* QMERGE_BLOCKERS: drop the soft-blocked installed packages the plan
		 * supersedes before merging (safe -U, shared-file protection on).
		 * This is the only place the resolver unmerges a package the user
		 * did not name; opt-in, soft (!) blocks only, blocked pkg installed. */
		if (qmerge_blockers && qm_soft_unmerge != NULL &&
				cnt_set(qm_soft_unmerge) > 0) {
			array  *bk = set_keys(qm_soft_unmerge);
			size_t  bn;
			char   *bp;

			warn("QMERGE_BLOCKERS: auto-unmerging %zu soft-blocked "
				 "package(s) before merging:", cnt_set(qm_soft_unmerge));
			array_for_each(bk, bn, bp)
				warn("  <<< %s", bp);
			array_free(bk);
			unmerge_packages(qm_soft_unmerge);
		}
		/* yank everything down concurrently first; the per-package
		 * fetch below then no-ops since the gpkg is already in PKGDIR
		 * (also helps --fetchonly, which is nothing but downloads).
		 * QMERGE_PREFETCH=false in make.conf/env disables the parallel
		 * stage; downloads then happen serially during the merge. */
		if (qmerge_prefetch)
			qm_prefetch(plan.merge, qmerge_jobs);

		array_for_each(plan.merge, i, cpvp) {
			atom_ctx     *a;
			tree_pkg_ctx *bpkg;
			char          exact[520];

			snprintf(exact, sizeof(exact), "=%s", cpvp);
			a = atom_explode(exact);
			if (a == NULL)
				continue;
			bpkg = best_version(a, BV_BINPKG);
			qm_mg_n     = i + 1;
			qm_mg_total = array_cnt(plan.merge);
			if (bpkg != NULL)
				pkg_fetch(0, a, bpkg);
			else
				warn("resolved package %s not found as a binpkg", cpvp);
			atom_implode(a);
		}
		qm_mg_n = qm_mg_total = 0;
	}

	array_deepfree(plan.merge, free);
	free_set(plan.in_merge);
	free_set(plan.examined);

	/* GLEP 42: surface any unread news, like portage's post-emerge notice */
	qm_news_notice();

	return rc;
}

/* Faithful port of Portage's vardbapi.get_counter_tick_core()
 * (lib/portage/dbapi/vartree.py): return a COUNTER value that is at
 * least one greater than both the global counter file and the highest
 * COUNTER of any installed package.  Trusting only the global file can
 * yield a value that is too low (e.g. after a restore), which corrupts
 * slot ordering and AUTOCLEAN because a freshly merged package would
 * carry a lower COUNTER than the version it replaces. */
static long
qm_get_counter_tick_core(void)
{
	char           path[_Q_PATH_MAX];
	char          *buf = NULL;   /* reused across all eat_file() calls */
	size_t         buf_len = 0;  /* both MUST start NULL/0 for eat_file */
	long           counter = -1;
	long           max_counter;
	DIR           *cat_dir;
	struct dirent *cat_de;

	/* 1. read the global counter file ($ROOT/var/cache/edb/counter) */
	snprintf(path, sizeof(path), "%s%s/counter", portroot, portedb);
	if (eat_file(path, &buf, &buf_len) && buf != NULL && buf[0] != '\0') {
		char *end;
		errno = 0;
		long v = strtol(buf, &end, 10);
		if (end != buf && errno == 0)
			counter = v;
		else
			warn("COUNTER file is corrupt: '%s'", path);
	}
	max_counter = counter;

	/* 2. scan every installed package's COUNTER, keep the maximum.
	 * $ROOT/var/db/pkg/<category>/<pf>/COUNTER */
	snprintf(path, sizeof(path), "%s%s", portroot, portvdb);
	if ((cat_dir = opendir(path)) != NULL) {
		while ((cat_de = readdir(cat_dir)) != NULL) {
			DIR           *pkg_dir;
			struct dirent *pkg_de;
			size_t         cat_len;

			if (cat_de->d_name[0] == '.')
				continue;
			cat_len = snprintf(path, sizeof(path), "%s%s/%s",
					portroot, portvdb, cat_de->d_name);
			if ((pkg_dir = opendir(path)) == NULL)
				continue;
			while ((pkg_de = readdir(pkg_dir)) != NULL) {
				if (pkg_de->d_name[0] == '.')
					continue;
				snprintf(path + cat_len, sizeof(path) - cat_len,
						"/%s/COUNTER", pkg_de->d_name);
				if (eat_file(path, &buf, &buf_len) &&
						buf != NULL && buf[0] != '\0') {
					char *end;
					errno = 0;
					long v = strtol(buf, &end, 10);
					if (end != buf && errno == 0 && v > max_counter)
						max_counter = v;
				}
			}
			closedir(pkg_dir);
		}
		closedir(cat_dir);
	}

	if (buf != NULL)
		free(buf);

	return max_counter + 1;
}

/* Port of Portage's counter_tick_core(incrementing=1): grab the next
 * COUNTER value and record it back to the global counter file so the
 * next install sees a strictly greater value.  Returns the new counter. */
static long
qm_counter_tick(void)
{
	char  path[_Q_PATH_MAX];
	char  tmp[_Q_PATH_MAX];
	long  counter = qm_get_counter_tick_core();
	FILE *fp;
	int   dir_len;

	/* write_atomic: write to a temp file then rename into place */
	dir_len = snprintf(path, sizeof(path), "%s%s", portroot, portedb);
	mkdir_p(path, 0755);
	snprintf(path + dir_len, sizeof(path) - dir_len, "/counter");
	snprintf(tmp, sizeof(tmp), "%.*s/counter.qmerge", dir_len, path);
	if ((fp = fopen(tmp, "w")) != NULL) {
		fprintf(fp, "%ld", counter);
		fclose(fp);
		if (rename(tmp, path) != 0) {
			warn("failed to update global counter %s", path);
			unlink(tmp);
		}
	} else {
		warn("failed to write global counter %s", tmp);
	}

	return counter;
}

/* GLEP 78/63/79 binary package signature posture, derived from FEATURES
 * exactly as Portage does (lib/portage/gpkg.py:793-822):
 *   verify  = check signatures when present (default on)
 *   request = signatures are mandatory (missing sig -> refuse)
 * binpkg-ignore-signature disables both; binpkg-request-signature makes
 * them mandatory.  (Per-repo binrepos.conf verify-signature override is a
 * later refinement; today only the FEATURES posture is honored.) */
static void
qm_sig_posture(bool *request, bool *verify)
{
	bool ign = contains_set("binpkg-ignore-signature", features) != NULL;
	bool req = contains_set("binpkg-request-signature", features) != NULL;

	*verify  = !ign;
	*request = req && !ign;
}

/* Portage's PORTAGE_TRUST_HELPER equivalent (bintree.py:_run_trust_helper):
 * before a run that will verify signatures, refresh the binpkg trust keyring
 * so gpgme has trusted keys to check against.  Runs only when signatures are
 * mandatory (binpkg-request-signature, or a repo with verify-signature=true),
 * we will actually merge (not pretend, not fetch-only) and we are root.
 * QMERGE_TRUST_HELPER selects the helper: unset = the built-in qetuto applet,
 * "false"/"no"/"0"/"" disables it (escape hatch), anything else is run via
 * the shell as an external command (point it at /usr/bin/getuto to defer to
 * app-portage/getuto).  qetuto self-throttles to once/day via .getuto.last,
 * so the common warm-cache cost is a single stat(). */
static void
qm_run_trust_helper(void)
{
	bool        request, verify, mandatory;
	size_t      ri;
	const char *th;
	pid_t       pid;
	int         st;

	if (pretend || fetch_only || geteuid() != 0)
		return;

	qm_sig_posture(&request, &verify);
	mandatory = request;
	for (ri = 0; !mandatory && ri < qm_nbinrepos; ri++)
		if (qm_binrepos[ri].verify_sig == 1)
			mandatory = true;
	if (!mandatory)
		return;

	th = getenv("QMERGE_TRUST_HELPER");
	if (th != NULL && (th[0] == '\0' ||
			strcmp(th, "false") == 0 || strcmp(th, "no") == 0 ||
			strcmp(th, "0") == 0))
		return;

	pid = fork();
	if (pid < 0)
		return;
	if (pid == 0) {
		if (th != NULL && th[0] != '\0') {
			execlp("sh", "sh", "-c", th, (char *)NULL);
			_exit(127);
		} else {
			char *av[3];
			int   n = 0;

			av[n++] = (char *)"qetuto";
			if (verbose > 0)
				av[n++] = (char *)"-v";
			av[n] = NULL;
			optind = 1;
			_exit(qetuto_main(n, av));
		}
	}
	if (waitpid(pid, &st, 0) < 0)
		return;
	if (!(WIFEXITED(st) && WEXITSTATUS(st) == 0))
		warn("trust helper did not complete successfully; OpenPGP "
			 "signature verification may fail");
}

#ifdef ENABLE_GPKG
/* GLEP 78: does this gpkg carry a signature at all?  True when any member
 * is a detached ".sig" file, or the Manifest is cleartext-signed. */
static bool
qm_gpkg_is_signed(const char *gpkg_path)
{
	struct archive       *a;
	struct archive_entry *e;
	bool                  is_signed = false;

	a = archive_read_new();
	archive_read_support_format_all(a);
	archive_read_support_filter_all(a);
	if (archive_read_open_filename(a, gpkg_path, BUFSIZ) != ARCHIVE_OK) {
		archive_read_free(a);
		return false;
	}
	while (archive_read_next_header(a, &e) == ARCHIVE_OK) {
		const char *nm = archive_entry_pathname(e);
		size_t      l  = nm != NULL ? strlen(nm) : 0;

		if (l >= 4 && strcmp(nm + l - 4, ".sig") == 0) {
			is_signed = true;
			break;
		}
		if (l >= 8 && strcmp(nm + l - 8, "Manifest") == 0) {
			char    peek[64];
			ssize_t n = archive_read_data(a, peek, sizeof(peek) - 1);
			if (n > 0) {
				peek[n] = '\0';
				if (strstr(peek, "BEGIN PGP SIGNED MESSAGE") != NULL) {
					is_signed = true;
					break;
				}
			}
		}
	}
	archive_read_free(a);
	return is_signed;
}

#ifdef HAVE_GPGME
/* Portage's dedicated binary-package trust keyring (maintained by getuto),
 * matching BINPKG_GPG_VERIFY_GPG_HOME's default. */
# define QM_GPG_HOME  "/etc/portage/gnupg"

/* Verify an OpenPGP signature with gpgme against the binpkg keyring.
 *   cleartext: sig = inline-signed blob, signed_data = NULL, plain gets text.
 *   detached:  sig = detached signature, signed_data = the data, plain = NULL.
 * Returns true iff the first signature is GOOD and TRUSTED (fully/ultimately
 * valid), the gpgme equivalent of Portage's GOODSIG + TRUST_ULTIMATE/FULLY. */
static bool
qm_gpg_verify(gpgme_data_t sig, gpgme_data_t signed_data, gpgme_data_t plain)
{
	static bool           inited = false;
	gpgme_ctx_t           ctx = NULL;
	gpgme_verify_result_t vr;
	gpgme_signature_t     s;
	bool                  ok = false;

	if (!inited) {
		gpgme_check_version(NULL);
		inited = true;
	}
	if (gpgme_new(&ctx) != GPG_ERR_NO_ERROR)
		return false;
	/* verify against Portage's binpkg keyring, not the caller's ~/.gnupg */
	gpgme_ctx_set_engine_info(ctx, GPGME_PROTOCOL_OpenPGP, NULL, QM_GPG_HOME);

	if (gpgme_op_verify(ctx, sig, signed_data, plain) == GPG_ERR_NO_ERROR) {
		vr = gpgme_op_verify_result(ctx);
		if (vr != NULL && (s = vr->signatures) != NULL)
			if (s->status == GPG_ERR_NO_ERROR &&
					(s->summary & GPGME_SIGSUM_VALID))
				ok = true;
	}
	gpgme_release(ctx);
	return ok;
}

/* gpgme streaming read callback: pull the current gpkg member's bytes
 * straight from libarchive, so large members are never buffered */
static ssize_t
qm_gpgme_read_cb(void *handle, void *buffer, size_t size)
{
	la_ssize_t n = archive_read_data((struct archive *)handle, buffer, size);
	return n < 0 ? -1 : (ssize_t)n;
}
#endif  /* HAVE_GPGME */

/* GLEP 78/63/79 OpenPGP signature verification of a signed gpkg, done by
 * STREAMING (no extract to disk, no whole-member buffering).  The container
 * structure and every member's checksum-against-Manifest are already
 * validated by qm_gpkg_check(); here we only establish trust:
 *   1. the Manifest must carry a good, trusted cleartext signature
 *   2. every signed member (all but gpkg-1) must have a detached .sig that
 *      verifies against its data
 * The signed Manifest plus the (already verified) checksum chain
 * authenticate the members; the detached sigs are portage's additional
 * belt-and-braces.  Returns true iff the package is trustworthy.
 * Runs inside the unprivileged child forked by qm_gpkg_verify(). */
static bool
qm_gpkg_verify_impl(const char *gpkg_path)
{
#ifdef HAVE_GPGME
	struct qm_sig { char *name; char *data; size_t len; };
	struct archive       *a;
	struct archive_entry *e;
	char                 *manifest = NULL;
	size_t                manifest_len = 0;
	array                *sigs = array_new();
	gpgme_data_t          md = NULL;
	gpgme_data_t          plain = NULL;
	bool                  ok = false;
	size_t                i;
	struct qm_sig        *sg;

	gpgme_check_version(NULL);

	/* pass 1: buffer the small members (Manifest + every detached .sig),
	 * skipping the large compressed payloads without reading them */
	a = archive_read_new();
	archive_read_support_format_all(a);
	archive_read_support_filter_all(a);
	if (archive_read_open_filename(a, gpkg_path, BUFSIZ) != ARCHIVE_OK) {
		archive_read_free(a);
		goto out;
	}
	while (archive_read_next_header(a, &e) == ARCHIVE_OK) {
		const char *nm = archive_entry_pathname(e);
		const char *base;
		size_t      blen;
		char        buf[BUFSIZ];
		la_ssize_t  n;

		if (nm == NULL) { archive_read_data_skip(a); continue; }
		base = strrchr(nm, '/');
		base = base != NULL ? base + 1 : nm;
		blen = strlen(base);

		if (strcmp(base, "Manifest") == 0) {
			while ((n = archive_read_data(a, buf, sizeof(buf))) > 0) {
				manifest = xrealloc(manifest, manifest_len + (size_t)n + 1);
				memcpy(manifest + manifest_len, buf, (size_t)n);
				manifest_len += (size_t)n;
			}
		} else if (blen >= 4 && strcmp(base + blen - 4, ".sig") == 0) {
			sg = xzalloc(sizeof(*sg));
			sg->name = xstrdup(base);
			while ((n = archive_read_data(a, buf, sizeof(buf))) > 0) {
				sg->data = xrealloc(sg->data, sg->len + (size_t)n);
				memcpy(sg->data + sg->len, buf, (size_t)n);
				sg->len += (size_t)n;
			}
			array_append(sigs, sg);
		} else {
			archive_read_data_skip(a);
		}
	}
	archive_read_free(a);

	if (manifest == NULL) {
		warn("%s: Manifest not found", gpkg_path);
		goto out;
	}

	/* 1. the Manifest must carry a good, trusted cleartext signature */
	if (gpgme_data_new_from_mem(&md, manifest, manifest_len, 1)
			!= GPG_ERR_NO_ERROR)
		goto out;
	if (gpgme_data_new(&plain) != GPG_ERR_NO_ERROR)
		goto out;
	if (!qm_gpg_verify(md, NULL, plain)) {
		warn("%s: Manifest signature missing, invalid, or from an "
				"untrusted key", gpkg_path);
		goto out;
	}

	/* 2. stream-verify every signed member's detached signature */
	a = archive_read_new();
	archive_read_support_format_all(a);
	archive_read_support_filter_all(a);
	if (archive_read_open_filename(a, gpkg_path, BUFSIZ) != ARCHIVE_OK)
		goto out;
	ok = true;
	while (ok && archive_read_next_header(a, &e) == ARCHIVE_OK) {
		const char           *nm = archive_entry_pathname(e);
		const char           *base;
		size_t                blen;
		char                  signame[512];
		struct qm_sig        *found = NULL;
		gpgme_data_t          sd = NULL;
		gpgme_data_t          dd = NULL;
		struct gpgme_data_cbs cbs;

		if (nm == NULL) { archive_read_data_skip(a); continue; }
		base = strrchr(nm, '/');
		base = base != NULL ? base + 1 : nm;
		blen = strlen(base);

		/* only the payload members carry detached signatures */
		if (strcmp(base, "Manifest") == 0 || strcmp(base, "gpkg-1") == 0 ||
				(blen >= 4 && strcmp(base + blen - 4, ".sig") == 0)) {
			archive_read_data_skip(a);
			continue;
		}

		snprintf(signame, sizeof(signame), "%s.sig", base);
		array_for_each(sigs, i, sg)
			if (strcmp(sg->name, signame) == 0) { found = sg; break; }
		if (found == NULL) {
			warn("%s: '%s' has no detached signature", gpkg_path, base);
			ok = false;
			break;
		}

		if (gpgme_data_new_from_mem(&sd, found->data, found->len, 1)
				!= GPG_ERR_NO_ERROR) {
			ok = false;
			break;
		}
		memset(&cbs, 0, sizeof(cbs));
		cbs.read = qm_gpgme_read_cb;
		if (gpgme_data_new_from_cbs(&dd, &cbs, a) != GPG_ERR_NO_ERROR) {
			gpgme_data_release(sd);
			ok = false;
			break;
		}
		/* gpgme streams the member (dd) straight from the archive */
		if (!qm_gpg_verify(sd, dd, NULL)) {
			warn("%s: detached signature for '%s' is invalid or untrusted",
					gpkg_path, base);
			ok = false;
		}
		gpgme_data_release(sd);
		gpgme_data_release(dd);
	}
	archive_read_free(a);

out:
	if (md != NULL)    gpgme_data_release(md);
	if (plain != NULL) gpgme_data_release(plain);
	free(manifest);
	array_for_each(sigs, i, sg) {
		free(sg->name);
		free(sg->data);
		free(sg);
	}
	array_free(sigs);
	return ok;
#else
	(void)gpkg_path;
	warn("built without gpgme: cannot verify binary package signatures");
	return false;
#endif
}

/* shed root -> nobody:nogroup so a booby-trapped signature can't exploit
 * gpg with our privileges (portage does the same, GPG_VERIFY_USER_DROP).
 * Best-effort: a failed drop just leaves us where we were. */
static void
qm_drop_privs(void)
{
	struct passwd *pw = getpwnam("nobody");
	struct group  *gr = getgrnam("nogroup");
	gid_t          gid = gr != NULL ? gr->gr_gid :
				(pw != NULL ? pw->pw_gid : (gid_t)65534);
	uid_t          uid = pw != NULL ? pw->pw_uid : (uid_t)65534;

	/* groups, then gid, then uid, can't reorder, uid drop is one-way.
	 * best-effort: a failed drop just verifies at the current privilege */
	if (setgroups(0, NULL) != 0)
		{ /* keep going; supplementary groups are the least of it */ }
	if (setgid(gid) != 0)
		warn("could not drop gid for signature verification");
	if (setuid(uid) != 0)
		warn("could not drop to nobody for signature verification");
}

/* Verify a signed gpkg with privileges dropped: when root, fork a child
 * that becomes nobody and runs the gpgme verification, and take its exit
 * status as the verdict.  A fork failure falls back to verifying in-
 * process (no worse than before).  Returns true iff trustworthy. */
static bool
qm_gpkg_verify(const char *gpkg_path)
{
	pid_t pid;
	int   status;

	if (geteuid() != 0)
		return qm_gpkg_verify_impl(gpkg_path);

	fflush(stdout);
	fflush(stderr);
	pid = fork();
	if (pid == 0) {
		qm_drop_privs();
		_exit(qm_gpkg_verify_impl(gpkg_path) ? 0 : 1);
	}
	if (pid < 0)
		return qm_gpkg_verify_impl(gpkg_path);  /* fork died; do it here */

	while (waitpid(pid, &status, 0) < 0 && errno == EINTR)
		;
	return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

/* streaming read callback pulling the current gpkg member's data */
static size_t
qm_archive_read_cb(char *dest, size_t destlen, void *ctx)
{
	la_ssize_t n = archive_read_data((struct archive *)ctx, dest, destlen);
	return n > 0 ? (size_t)n : 0;
}

struct qm_gmember {
	char      *base;
	char       sha512[BLAKE2B_DIGEST_LENGTH + 1];
	char       blake2b[BLAKE2B_DIGEST_LENGTH + 1];
	long long  size;
	bool       verified;
};

/* GLEP 78 container hardening + Manifest checksum verification, run on
 * EVERY gpkg (signed or not) before decompression, matching portage's
 * _verify_binpkg (lib/portage/gpkg.py).  Members are hashed by streaming
 * (no extract to disk), so large packages are not buffered.  Checks:
 *   - gpkg-1 version marker present
 *   - every member: not absolute, exactly one directory level, a single
 *     shared prefix dir, a regular file, no duplicate names
 *   - Manifest present; each member's size and at least one supported
 *     digest (SHA512/BLAKE2B) match it; no member missing from or unknown
 *     to the Manifest
 * Returns true iff the container is well-formed and intact. */
static bool
qm_gpkg_check(const char *gpkg_path)
{
	struct archive       *a;
	struct archive_entry *e;
	array                *members = array_new();
	set                  *seen    = create_set();
	char                 *manifest = NULL;
	char                 *prefix   = NULL;
	bool                  gpkg1    = false;
	bool                  ok       = true;
	size_t                i;
	struct qm_gmember    *m;

	a = archive_read_new();
	archive_read_support_format_all(a);
	archive_read_support_filter_all(a);
	if (archive_read_open_filename(a, gpkg_path, BUFSIZ) != ARCHIVE_OK) {
		archive_read_free(a);
		free_set(seen);
		array_free(members);
		return false;
	}

	while (ok && archive_read_next_header(a, &e) == ARCHIVE_OK) {
		const char *name = archive_entry_pathname(e);
		const char *slash;
		const char *base;
		size_t      dirlen;

		if (name == NULL || name[0] == '/') {
			warn("%s: member with absolute path", gpkg_path);
			ok = false; break;
		}
		slash = strchr(name, '/');
		if (slash == NULL || strchr(slash + 1, '/') != NULL) {
			warn("%s: member not at exactly one directory level: %s",
					gpkg_path, name);
			ok = false; break;
		}
		if (archive_entry_filetype(e) != AE_IFREG) {
			warn("%s: non-regular member: %s", gpkg_path, name);
			ok = false; break;
		}
		if (contains_set(name, seen) != NULL) {
			warn("%s: duplicate member '%s' (possible same-name attack)",
					gpkg_path, name);
			ok = false; break;
		}
		add_set(name, seen);

		dirlen = (size_t)(slash - name);
		if (prefix == NULL) {
			prefix = xmalloc(dirlen + 1);
			memcpy(prefix, name, dirlen);
			prefix[dirlen] = '\0';
		} else if (strncmp(name, prefix, dirlen) != 0 ||
				prefix[dirlen] != '\0') {
			warn("%s: members do not share a single prefix directory",
					gpkg_path);
			ok = false; break;
		}

		base = slash + 1;
		if (*base == '\0')
			continue;
		if (strcmp(base, "gpkg-1") == 0)
			gpkg1 = true;

		if (strcmp(base, "Manifest") == 0) {
			char       buf[BUFSIZ];
			size_t     mlen = 0;
			size_t     cap  = 0;
			la_ssize_t n;
			while ((n = archive_read_data(a, buf, sizeof(buf))) > 0) {
				if (mlen + (size_t)n + 1 > cap) {
					cap = (mlen + (size_t)n + 1) * 2;
					manifest = xrealloc(manifest, cap);
				}
				memcpy(manifest + mlen, buf, (size_t)n);
				mlen += (size_t)n;
			}
			manifest = xrealloc(manifest, mlen + 1);
			manifest[mlen] = '\0';
			continue;
		}

		m = xzalloc(sizeof(*m));
		m->base = xstrdup(base);
		{
			size_t flen = 0;
			hash_multiple_cb(qm_archive_read_cb, a, NULL, NULL, NULL,
					m->sha512, m->blake2b, &flen, HASH_SHA512 | HASH_BLAKE2B);
			m->size = (long long)flen;
		}
		array_append(members, m);
	}
	archive_read_free(a);

	if (ok && !gpkg1) {
		warn("%s: missing gpkg-1 version marker", gpkg_path);
		ok = false;
	}
	if (ok && manifest == NULL) {
		warn("%s: Manifest not found", gpkg_path);
		ok = false;
	}

	/* cross-check the Manifest against the members (both directions) */
	if (ok) {
		char *mcopy = xstrdup(manifest);
		char *savep;
		char *line;

		for (line = strtok_r(mcopy, "\n", &savep);
				ok && line != NULL;
				line = strtok_r(NULL, "\n", &savep))
		{
			char              buf[BUFSIZ];
			char             *toks[24];
			int               ntok = 0;
			char             *tok;
			char             *sp;
			struct qm_gmember *found = NULL;
			long long         msize;
			int               k;
			int               matched = 0;

			if (strncmp(line, "DATA ", 5) != 0)
				continue;
			snprintf(buf, sizeof(buf), "%s", line);
			for (tok = strtok_r(buf, " \t", &sp);
					tok != NULL && ntok < (int)(sizeof(toks) / sizeof(toks[0]));
					tok = strtok_r(NULL, " \t", &sp))
				toks[ntok++] = tok;
			if (ntok < 3)  /* DATA name size ... */
				continue;

			array_for_each(members, i, m)
				if (strcmp(m->base, toks[1]) == 0) { found = m; break; }
			if (found == NULL) {
				warn("%s: Manifest lists '%s' but it is missing from the "
						"package", gpkg_path, toks[1]);
				ok = false; break;
			}

			msize = strtoll(toks[2], NULL, 10);
			if (msize != found->size) {
				warn("%s: '%s' size mismatch vs Manifest", gpkg_path,
						toks[1]);
				ok = false; break;
			}

			/* walk "HASHNAME hex" pairs; every supported hash listed must
			 * match, and at least one supported hash must be present */
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
	}

	/* any member not covered by the Manifest is an unknown file */
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

	array_for_each(members, i, m) {
		free(m->base);
		free(m);
	}
	array_free(members);
	free_set(seen);
	free(manifest);
	free(prefix);
	return ok;
}
#endif  /* ENABLE_GPKG */

/* oh shit getting into pkg mgt here. FIXME: write a real dep resolver. */
static bool
qm_binpkg_is_gpkg(const char *path)
{
	size_t plen = strlen(path);
	int    fd;
	char   tail[4];
	bool   gpkg = false;

	/* the gpkg suffix is authoritative; xpak suffixes are verified by
	 * content so a misnamed gpkg still routes correctly */
	if (plen > sizeof(".gpkg.tar") - 1 &&
			memcmp(path + plen - (sizeof(".gpkg.tar") - 1),
				   ".gpkg.tar", sizeof(".gpkg.tar") - 1) == 0)
		return true;

	/* content sniff, portage get_binpkg_format parity: xpak ends with
	 * a literal STOP marker */
	fd = open(path, O_RDONLY | O_CLOEXEC);
	if (fd < 0)
		return false;
	if (lseek(fd, -4, SEEK_END) >= 0 &&
			read(fd, tail, 4) == 4 &&
			memcmp(tail, "STOP", 4) == 0) {
		close(fd);
		return false;
	}
	close(fd);

	/* a tar whose early members include gpkg-1 is a gpkg */
	{
		struct archive       *a = archive_read_new();
		struct archive_entry *e;
		int                   n = 0;

		archive_read_support_format_tar(a);
		archive_read_support_filter_all(a);
		if (archive_read_open_filename(a, path, 65536) == ARCHIVE_OK) {
			while (n++ < 8 &&
				   archive_read_next_header(a, &e) == ARCHIVE_OK) {
				const char *nm = archive_entry_pathname(e);
				const char *bn = nm != NULL ? strrchr(nm, '/') : NULL;

				bn = bn != NULL ? bn + 1 : nm;
				if (bn != NULL && strcmp(bn, "gpkg-1") == 0) {
					gpkg = true;
					break;
				}
				archive_read_data_skip(a);
			}
		}
		archive_read_free(a);
	}
	return gpkg;
}

static void
pkg_merge(int level, const depend_atom *qatom, tree_pkg_ctx *mpkg)
{
	set            *objs;
	tree_pkg_ctx   *previnst;
	array          *slotmembers = NULL;
	atom_ctx       *matom;
	FILE           *fp;
	FILE           *contents;
	char            buf[_Q_PATH_MAX];
	char           *p;
	char           *D;
	char           *T;
	struct stat     st;
	char          **iargv;
	int             iargc;
	int             cp_argc;
	int             cpm_argc;
	char          **cp_argv;
	char          **cpm_argv;
	int             tbz2size;
	const char     *replver       = "";
	int             replacing     = NOT_EQUAL;
	char           *eprefix       = NULL;
	size_t          eprefix_len   = 0;
	char           *pm_phases     = NULL;
	size_t          pm_phases_len = 0;
	char           *eapi          = NULL;
	size_t          eapi_len      = 0;

	if ((!install && !fetch_only) || !mpkg || !qatom)
		return;

	/* full atom of the package being merged, carrying its SLOT */
	matom = tree_pkg_atom(mpkg, true);

	if (level == 0 && !pretend)
		qm_elog(" >>> emerge (%zu of %zu) %s to %s",
				qm_mg_total > 0 ? qm_mg_n : 1,
				qm_mg_total > 0 ? qm_mg_total : 1,
				atom_format("%[CAT]%[PF]", matom), portroot);

	/* Portage treats a SLOT as holding exactly one package: installing
	 * into a slot replaces ALL installed members of that slot, not just
	 * the highest version (vardbapi/depgraph one-package-per-slot rule).
	 * Enumerate every installed member so stray versions left behind by a
	 * previous botched install get collapsed too, matching emerge and
	 * preventing lingering double-installs. */
	previnst = NULL;
	slotmembers = qm_slot_members(matom->CATEGORY, matom->PN, matom->SLOT);
	if (slotmembers != NULL && array_cnt(slotmembers) > 0) {
		size_t         n;
		tree_pkg_ctx  *m;
		atom_ctx      *lowatom = NULL;

		/* pick the lowest-versioned member as the "replaced" version for
		 * the [R]/[U]/[D] label, emerge shows the meaningful transition
		 * from the oldest slot member (e.g. [U] foo-22 [21], not [R]) */
		array_for_each(slotmembers, n, m) {
			atom_ctx *ma = tree_pkg_atom(m, false);
			/* drop REPO and SUBSLOT: SUBSLOT only affects rebuild
			 * triggering, REPO is irrelevant for slot occupancy */
			if (lowatom == NULL ||
					atom_compare_flg(ma, lowatom,
						ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO) == OLDER) {
				previnst = m;
				lowatom  = ma;
			}
		}
		if (lowatom != NULL) {
			replacing = atom_compare_flg(matom, lowatom,
										 ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO);
			replver   = lowatom->PVR;
		}
	}

	(void)qprint_tree_node(level, mpkg, previnst, replacing);


	/* --fetchonly: everything needed is in PKGDIR now, the rdepends
	 * walk above has fetched the dependencies as well */
	if (fetch_only)
		return;

	if (pretend == 100) {
		return;
	}

	/* create directories in the vdb repo */
	if (!pretend)
	{
		snprintf(buf, sizeof(buf), "%s/%s/%s",
				 portroot, portvdb, matom->CATEGORY);
		if (mkdir_p(buf, 0755) != 0)
			errp("cannot create VDB directory %s", buf);
	}

	/* Set up our temp dir to unpack this stuff   FIXME p -> builddir */
	snprintf(buf, sizeof(buf), "%s%s/qmerge/%s/%s",
			 portroot, port_tmpdir, matom->CATEGORY, matom->PF);
	if (mkdir_p(buf, 0755) != 0)
		errp("cannot create work directory %s", buf);
	xchdir(buf);
	xasprintf(&D, "%s/image", buf);
	xasprintf(&T, "%s/temp", buf);

	/* Doesn't actually remove $PWD, just everything under it */
	rm_rf(".");

	mkdir("temp", 0755);
	mkdir("vdb", 0755);
	mkdir("image", 0755);

	p = tree_pkg_get_path(mpkg);
	/* p is portroot-relative and cwd is the build tempdir here */
	snprintf(buf, sizeof(buf), "%s/%s", portroot, p);
	if (qm_binpkg_is_gpkg(buf))
	{
#ifdef ENABLE_GPKG
		/* unpack the whole thing to temp, dropping the pkg name dir, so
		 * we end up with generic files in temp */
		struct archive       *a;
		struct archive       *t;
		struct archive_entry *entry;

		/* construct full path */
		snprintf(buf, sizeof(buf), "%s/%s", portroot, p);

		/* GLEP 78/63/79: verify signatures BEFORE decompressing anything.
		 * Portage never extracts a package whose signature is required but
		 * missing/invalid (gpkg.py verifies ahead of extractall). */
		{
			bool        sig_request, sig_verify;
			bool        sig_present;
			ssize_t     sig_repo = qm_repoidx_of_pkg(mpkg);
			const char *sig_why  = "binpkg-request-signature";

			qm_sig_posture(&sig_request, &sig_verify);
			/* binrepos.conf verify-signature overrides the FEATURES
			 * posture for packages served by that repo (portage
			 * >=3.0.74): true = mandatory, false = skip entirely */
			if (sig_repo >= 0 && qm_nbinrepos > 0) {
				int vs = qm_binrepos[sig_repo].verify_sig;

				if (vs == 1) {
					sig_request = true;
					sig_verify  = true;
					sig_why     = "binrepos.conf verify-signature=true";
				} else if (vs == 0) {
					sig_request = false;
					sig_verify  = false;
				}
			}
			sig_present = qm_gpkg_is_signed(buf);

#ifndef HAVE_GPGME
			/* built without gpgme: we can see whether a signature is
			 * present but cannot verify it.  Don't pretend to enforce --
			 * refuse only when signatures are mandatory, otherwise install
			 * unverified (same posture as binpkg-ignore-signature). */
			if (sig_request)
				err("%s: %s but this q was built "
					"without OpenPGP support (USE=gpg); cannot verify signatures",
					atom_format("%[CAT]%[PF]", matom), sig_why);
			sig_verify = false;
#endif

			if (sig_request && !sig_present)
				err("%s carries no OpenPGP signature but "
					"%s is enabled; refusing to merge",
					atom_format("%[CAT]%[PF]", matom), sig_why);
			/* GLEP 78 container hardening + Manifest checksum verification,
			 * on every package before we decompress anything */
			if (!qm_gpkg_check(buf))
				err("%s failed binary package integrity checks; refusing "
					"to merge", atom_format("%[CAT]%[PF]", matom));
			/* verify a signed package before we decompress it; on failure
			 * refuse (GLEP 78 MUST NOT decompress a bad signature) */
			if (sig_present && sig_verify && !qm_gpkg_verify(buf))
				err("%s failed OpenPGP signature verification; refusing "
					"to merge", atom_format("%[CAT]%[PF]", matom));
		}

		xchdir("temp");
		a = archive_read_new();
		t = archive_write_disk_new();
		archive_read_support_format_all(a);
		if (archive_read_open_filename(a, buf, BUFSIZ) != ARCHIVE_OK)
			err("failed to open %s: %s", buf, archive_error_string(a));
		while (archive_read_next_header(a, &entry) == ARCHIVE_OK) {
			const char *fname = archive_entry_pathname(entry);
			size_t      size;
			la_int64_t  off;

			/* drop pkg name dir prefix */
			fname = strchr(fname, '/');
			if (fname == NULL)
				continue;
			fname++;
			if (*fname == '\0')
				continue;  /* bug #968185 */

			/* GLEP 78 signature members (metadata.tar.xz.sig etc.) are
			 * verified straight from the gpkg above; extracting them
			 * here would clobber the metadata/image files below */
			{
				size_t flen = strlen(fname);

				if (flen > 4 && strcmp(fname + flen - 4, ".sig") == 0)
					continue;
			}

			/* drop compressor (and "tar", not to be misleading) for
			 * easy access below */
			if (strncmp(fname, "metadata.tar", sizeof("metadata.tar") - 1) == 0)
				fname = "metadata";
			if (strncmp(fname, "image.tar", sizeof("image.tar") - 1) == 0)
				fname = "image";

			archive_entry_set_pathname(entry, fname);
			fname = archive_entry_pathname(entry);  /* re-retrieve for errors */

			if (archive_write_header(t, entry) != ARCHIVE_OK)
				err("failed to unpack from gpkg '%s': %s",
					fname, archive_error_string(t));
			while (archive_read_data_block(a, (const void **)&p,
										   &size, &off) == ARCHIVE_OK)
			{
				if (archive_write_data_block(t, p, size, off) != ARCHIVE_OK)
					err("failed to write from gpkg '%s': %s\n",
						fname, archive_error_string(t));
			}
			archive_write_finish_entry(t);
		}
		archive_read_close(a);
		archive_read_free(a);
		archive_write_close(t);
		archive_write_free(t);
		xchdir("..");

		/* now we unpacked everything, we can extract the VDB (metadata)
		 * and image */
		xchdir("vdb");
		a = archive_read_new();
		t = archive_write_disk_new();
		archive_read_support_format_all(a);
		archive_read_support_filter_all(a);
		archive_write_disk_set_options(t, (ARCHIVE_EXTRACT_PERM |
									   	   ARCHIVE_EXTRACT_TIME |
									   	   ARCHIVE_EXTRACT_ACL |
									   	   ARCHIVE_EXTRACT_FFLAGS |
									   	   ARCHIVE_EXTRACT_XATTR));
		if (archive_read_open_filename(a, "../temp/metadata",
									   BUFSIZ) != ARCHIVE_OK)
			err("failed to open metadata: %s", archive_error_string(a));
		while (archive_read_next_header(a, &entry) == ARCHIVE_OK) {
			const char *fname = archive_entry_pathname(entry);
			size_t      size;
			la_int64_t  off;

			/* drop metadata prefix */
			fname = strchr(fname, '/');
			if (fname == NULL)
				continue;
			fname++;
			if (*fname == '\0')
				continue;  /* bug #968185 */

			archive_entry_set_pathname(entry, fname);
			fname = archive_entry_pathname(entry);  /* re-retrieve for errors */

			if (archive_write_header(t, entry) != ARCHIVE_OK)
				err("failed to unpack metadata '%s': %s",
					fname, archive_error_string(t));
			while (archive_read_data_block(a, (const void **)&p,
										   &size, &off) == ARCHIVE_OK)
			{
				if (archive_write_data_block(t, p, size, off) != ARCHIVE_OK)
					err("failed to write metadata '%s': %s\n",
						fname, archive_error_string(t));
			}
			archive_write_finish_entry(t);
		}
		archive_read_close(a);
		archive_read_free(a);
		archive_write_close(t);
		archive_write_free(t);
		xchdir("..");

		/* finally the image */
		xchdir("image");
		a = archive_read_new();
		t = archive_write_disk_new();
		archive_read_support_format_all(a);
		archive_read_support_filter_all(a);
		archive_write_disk_set_options(t, (ARCHIVE_EXTRACT_PERM |
									   	   ARCHIVE_EXTRACT_TIME |
									   	   ARCHIVE_EXTRACT_ACL |
									   	   ARCHIVE_EXTRACT_FFLAGS |
									   	   ARCHIVE_EXTRACT_XATTR));
		if (archive_read_open_filename(a, "../temp/image",
									   BUFSIZ) != ARCHIVE_OK)
			err("failed to open metadata: %s", archive_error_string(a));
		while (archive_read_next_header(a, &entry) == ARCHIVE_OK) {
			const char *fname = archive_entry_pathname(entry);
			size_t      size;
			la_int64_t  off;

			/* drop image prefix */
			fname = strchr(fname, '/');
			if (fname == NULL)
				continue;
			fname++;
			if (*fname == '\0')
				continue;  /* bug #968185 */

			archive_entry_set_pathname(entry, fname);
			fname = archive_entry_pathname(entry);  /* re-retrieve for errors */

			/* handle hardlinks offset, #968291 */
#ifdef HAVE_ARCHIVE_ENTRY_HARDLINK_IS_SET
			if (archive_entry_hardlink_is_set(entry))
#else
			/* for Ubuntu, older libarchive has no
			 * archive_entry_hardlink_is_set */
			if (archive_entry_hardlink(entry) != NULL)
#endif
			{
				const char *hlinktrg = archive_entry_hardlink(entry);
				/* drop image prefix like for the path */
				hlinktrg = strchr(hlinktrg, '/');
				if (hlinktrg == NULL ||
					hlinktrg[1] == '\0')
				{  /* really, how? */
					warn("%s has invalid hardlink target '%s', skipping",
						 fname, archive_entry_hardlink(entry));
					continue;
				}
				archive_entry_set_hardlink(entry, &hlinktrg[1]);
			}

			if (archive_write_header(t, entry) != ARCHIVE_OK)
				err("failed to unpack image '%s': %s",
					fname, archive_error_string(t));
			while (archive_read_data_block(a, (const void **)&p,
										   &size, &off) == ARCHIVE_OK)
			{
				if (archive_write_data_block(t, p, size, off) != ARCHIVE_OK)
					err("failed to write image '%s': %s\n",
						fname, archive_error_string(t));
			}
			archive_write_finish_entry(t);
		}
		archive_read_close(a);
		archive_read_free(a);
		archive_write_close(t);
		archive_write_free(t);
		xchdir("..");
#else
		err("gpkg support not compiled in for %s", p);
#endif
	} else {
		int             vdbfd;
		int             mfd;
		file_magic_type fmt;

		/* construct full path */
		snprintf(buf, sizeof(buf), "%s/%s", portroot, p);

		tbz2size = 0;
		if ((vdbfd = open("vdb", O_RDONLY)) == -1)
			err("failed to open vdb extraction directory");
		tbz2size = xpak_extract(buf, &vdbfd, pkg_extract_xpak_cb);
		close(vdbfd);
		if (tbz2size <= 0)
			err("%s appears not to be a valid tbz2 file", p);

		/* figure out if the data is compressed differently from what
		 * the name suggests, bug #660508, usage of BINPKG_COMPRESS */
		mfd = open(buf, O_RDONLY);
		fmt = file_magic_guess_fd(mfd);
		if (mfd >= 0)
			close(mfd);

		if (fmt == FMAGIC_UNKNOWN) {
			/* no magic matched: brotli (no magic header) is the only
			 * compressor libarchive cannot handle, fall back to an
			 * external decompress pipeline for it */
			FILE          *tarpipe;
			FILE          *tbz2f;
			unsigned char  iobuf[8192];
			int            piped = 0;
			int            perr;
			size_t         n;
			size_t         rd;
			size_t         wr;

			snprintf(buf, sizeof(buf),
				BUSYBOX " sh -c 'brotli -dc | tar -x%sf - -C image/'",
				((verbose > 1) ? "v" : ""));

			if ((tarpipe = popen(buf, "w")) == NULL)
				errp("failed to start %s", buf);

			snprintf(buf, sizeof(buf), "%s/%s", portroot, p);
			if ((tbz2f = fopen(buf, "r")) == NULL)
				errp("failed to open %s for reading", p);

			for (piped = wr = 0; piped < tbz2size; piped += wr) {
				n = MIN(tbz2size - piped, (ssize_t)sizeof iobuf);
				rd = fread(iobuf, 1, n, tbz2f);
				if (0 == rd) {
					if ((perr = ferror(tbz2f)) != 0)
						errp("reading %s failed", p);

					if (feof(tbz2f))
						err("unexpected EOF in %s: corrupted binpkg", p);
				}

				for (wr = n = 0; wr < rd; wr += n) {
					n = fwrite(iobuf + wr, 1, rd - wr, tarpipe);
					if (n != rd - wr) {
						if ((perr = ferror(tarpipe)) != 0)
							errp("failed to unpack binpkg");

						if (feof(tarpipe))
							err("unexpected EOF trying to unpack binpkg");
					}
				}
			}

			fclose(tbz2f);

			perr = pclose(tarpipe);
			if (perr > 0)
				err("finishing unpack binpkg exited with status %d", perr);
			else if (perr < 0)
				errp("finishing unpack binpkg unsuccessful");
		} else {
			/* known compression: extract in-process via libarchive,
			 * bounded to the tar bytes preceding the xpak trailer */
			struct archive       *a;
			struct archive       *t;
			struct archive_entry *entry;
			struct qm_tar_stream  stream;
			const void           *dblk;
			size_t                dsize;
			la_int64_t            doff;
			int                   r;

			if ((stream.f = fopen(buf, "r")) == NULL)
				errp("failed to open %s for reading", p);
			stream.left = (size_t)tbz2size;

			xchdir("image");
			a = archive_read_new();
			t = archive_write_disk_new();
			archive_read_support_format_tar(a);
			archive_read_support_filter_all(a);
			archive_write_disk_set_options(t, (ARCHIVE_EXTRACT_PERM |
											   ARCHIVE_EXTRACT_TIME |
											   ARCHIVE_EXTRACT_ACL |
											   ARCHIVE_EXTRACT_FFLAGS |
											   ARCHIVE_EXTRACT_XATTR));
			if (archive_read_open(a, &stream, NULL,
								  qm_tar_read_cb, NULL) != ARCHIVE_OK)
				err("failed to open binpkg %s: %s",
					p, archive_error_string(a));
			while ((r = archive_read_next_header(a, &entry)) == ARCHIVE_OK) {
				if (archive_write_header(t, entry) != ARCHIVE_OK)
					err("failed to unpack binpkg '%s': %s",
						archive_entry_pathname(entry),
						archive_error_string(t));
				while (archive_read_data_block(a, &dblk,
											   &dsize, &doff) == ARCHIVE_OK)
				{
					if (archive_write_data_block(t, dblk,
												 dsize, doff) != ARCHIVE_OK)
						err("failed to write binpkg '%s': %s\n",
							archive_entry_pathname(entry),
							archive_error_string(t));
				}
				archive_write_finish_entry(t);
			}
			if (r != ARCHIVE_EOF)
				err("failed to unpack binpkg %s: %s",
					p, archive_error_string(a));
			archive_read_close(a);
			archive_read_free(a);
			archive_write_close(t);
			archive_write_free(t);
			fclose(stream.f);
			xchdir("..");
		}
	}

	fflush(stdout);

	/* we won't realloc, so we can loose the alloc size */
	eprefix_len = eat_file("vdb/EPREFIX", &eprefix, &eprefix_len) ?
		strlen(eprefix) : 0;
	/* don't care/use the string lengths on these */
	eat_file("vdb/EAPI", &eapi, &eapi_len);
	eat_file("vdb/DEFINED_PHASES", &pm_phases, &pm_phases_len);

	if (!pretend) {
		pkg_run_func("vdb", pm_phases, PKG_PRETEND, D, T, eapi, replver);
		pkg_run_func("vdb", pm_phases, PKG_SETUP,   D, T, eapi, replver);
		pkg_run_func("vdb", pm_phases, PKG_PREINST, D, T, eapi, replver);
	}

	{
		int imagefd = open("image", O_RDONLY);
		size_t masklen = strlen(install_mask) + 1 +
				strlen(pkg_install_mask) + 1 +
				15 + 1 + 14 + 1 + 14 + 1 + 1;  /* worst case scenario */
		char *imask;
		size_t maskp;

		if (imagefd == -1) {
			err("Failed to open image dir");
		} else if (fstat(imagefd, &st) == -1) {
			close(imagefd);
			err("Cannot stat image dirfd");
		} else if (eprefix != NULL && eprefix[0] == '/') {
			int imagepfx = openat(imagefd, eprefix + 1, O_RDONLY);
			if (imagepfx != -1) {
				close(imagefd);
				imagefd = imagepfx;
			}
		}

		imask = xmalloc(masklen);
		/* rely on INSTALL_MASK code to remove optional dirs */
				/* PKG_INSTALL_MASK: applied only at install-from-binpkg time (the
		 * binpkg keeps the files, they are masked per-host on merge), same
		 * negation/glob semantics as INSTALL_MASK since they share the code */
		maskp = snprintf(imask, masklen, "%s ", install_mask);
		if (pkg_install_mask != NULL && *pkg_install_mask != '\0')
			maskp += snprintf(imask + maskp, masklen - maskp,
					"%s ", pkg_install_mask);
		if (contains_set("noinfo", features))
			maskp += snprintf(imask + maskp, masklen - maskp,
					"/usr/share/info ");
		if (contains_set("noman", features))
			maskp += snprintf(imask + maskp, masklen - maskp,
					"/usr/share/man ");
		if (contains_set("nodoc", features))
			maskp += snprintf(imask + maskp, masklen - maskp,
					"/usr/share/doc ");

		/* Initialize INSTALL_MASK and common stuff */
		makeargv(imask, &iargc, &iargv);
		free(imask);
		install_mask_pwd(iargc, iargv, &st, imagefd);
		freeargv(iargc, iargv);

		/* we dont care about the return code, if it's empty, we want it
		 * gone */
		unlinkat(imagefd, "./usr/share", AT_REMOVEDIR);

		close(imagefd);
	}

	makeargv(config_protect, &cp_argc, &cp_argv);
	makeargv(config_protect_mask, &cpm_argc, &cpm_argv);

	/* call pkg_prerm right before we merge the replacement version such
	 * that any logic it defines, can use stuff installed by the package */
	switch (replacing) {
		case NEWER:
		case OLDER:
		case EQUAL:
			if (!pretend)
				pkg_run_func("vdb", pm_phases, PKG_PRERM, D, T, eapi, replver);
			break;
		default:
			warn("no idea how we reached here.");
		case ERROR:
		case NOT_EQUAL:
			break;
	}

	objs = NULL;
	if ((contents = fopen("vdb/CONTENTS", "w")) == NULL) {
		errf("could not open vdb/CONTENTS for writing");
	} else {
		char *cpath;
		int ret;

		cpath = xstrdup("");  /* xrealloced in merge_tree_at */

		/* TODO: use replacing to pass over pervinst->pkg for
		 * VDB/CONTENTS and respect the config-protect-if-modified flag
		 * like unmerge does */

		ret = merge_tree_at(AT_FDCWD, "image",
				AT_FDCWD, portroot, contents, eprefix_len,
				&objs, &cpath, cp_argc, cp_argv, cpm_argc, cpm_argv);

		free(cpath);

		if (ret != 0)
			errp("failed to merge to %s", portroot);

		fclose(contents);
	}

	/* Unmerge any stray pieces from the versions we replaced.  A slot
	 * holds one package, so remove EVERY installed member of the slot
	 * (there is normally one; more only when a prior install corrupted
	 * the slot).  Files owned by the incoming package (objs) are kept, so
	 * shared files are never deleted, this is what makes collapsing a
	 * double-install safe, unlike a bare unmerge. */
	switch (replacing) {
		case NEWER:
		case OLDER:
		case EQUAL:
			/* We need to really set this unmerge pending after we
			 * look at contents of the new pkg */
			if (slotmembers != NULL) {
				size_t        n;
				tree_pkg_ctx *m;
				array_for_each(slotmembers, n, m)
					pkg_unmerge(m, matom, objs,
							cp_argc, cp_argv, cpm_argc, cpm_argv);
			}
			break;
		default:
			warn("no idea how we reached here.");
		case ERROR:
		case NOT_EQUAL:
			break;
	}
	if (slotmembers != NULL) {
		array_free(slotmembers);  /* frees the array, not the tree-owned ctxs */
		slotmembers = NULL;
	}

	/* run postinst */
	if (!pretend)
		pkg_run_func("vdb", pm_phases, PKG_POSTINST, D, T, eapi, replver);

	if (eprefix != NULL)
		free(eprefix);
	if (eapi != NULL)
		free(eapi);
	if (pm_phases != NULL)
		free(pm_phases);

	freeargv(cp_argc, cp_argv);
	freeargv(cpm_argc, cpm_argv);

	/* Clean up the package state */
	if (objs != NULL)
		free_set(objs);
	free(D);
	free(T);

	/* Update the magic counter.  Portage assigns every install a unique,
	 * strictly increasing COUNTER (vardbapi.counter_tick_core); a value
	 * that is too low corrupts slot ordering and AUTOCLEAN.  Only tick the
	 * global counter for a real merge, pretend must not mutate the DB. */
	if (!pretend) {
		long counter = qm_counter_tick();
		if ((fp = fopen("vdb/COUNTER", "w")) != NULL) {
			fprintf(fp, "%ld", counter);
			fclose(fp);
		}
	}

	/* Record BINPKGMD5: the md5 of the binary package we installed from,
	 * exactly as Portage does (lib/_emerge/Binpkg.py).  It lets Portage
	 * identify which binpkg instance produced this install and detect a
	 * same-version rebuild (different content). */
	if (!pretend) {
		char  *bpp = tree_pkg_get_path(mpkg);
		char  *md5;
		if (bpp != NULL) {
			/* same construction the unpack path uses above */
			snprintf(buf, sizeof(buf), "%s/%s", portroot, bpp);
			/* hash_file returns a static buffer, do not free it */
			md5 = hash_file(buf, HASH_MD5);
			if (md5 != NULL) {
				if ((fp = fopen("vdb/BINPKGMD5", "w")) != NULL) {
					fprintf(fp, "%s\n", md5);
					fclose(fp);
				}
			}
		}
	}

	/* Record INSTALL_MASK actually applied, matching Portage
	 * (lib/portage/dbapi/bintree.py); used for reinstall detection when
	 * the mask changes. */
	if (!pretend && install_mask != NULL) {
		if ((fp = fopen("vdb/INSTALL_MASK", "w")) != NULL) {
			fprintf(fp, "%s\n", install_mask);
			fclose(fp);
		}
	}

	if (!pretend) {
		size_t len;
		/* move the local vdb copy to the final place */
		len = snprintf(buf, sizeof(buf), "%s%s/%s",
				portroot, portvdb, matom->CATEGORY);
		mkdir_p(buf, 0755);
		snprintf(buf + len, sizeof(buf) - len, "/%s", matom->PF);
		rm_rf(buf);  /* get rid of existing dir, empty dir is fine */
		if (rename("vdb", buf) != 0) {
			struct stat     vst;
			int             src_fd;
			int             dst_fd;
			int             cnt;
			int             vi;
			struct dirent **files;

			/* e.g. in case of cross-device rename, try copy+delete */
			if ((src_fd = open("vdb", O_RDONLY|O_CLOEXEC|O_PATH)) < 0 ||
				fstat(src_fd, &vst) != 0 ||
				mkdir_p(buf, vst.st_mode) != 0 ||
				(dst_fd = open(buf, O_RDONLY|O_CLOEXEC|O_PATH)) < 0 ||
				(cnt = scandirat(src_fd, ".",
								 &files, filter_self_parent, NULL)) < 0)
			{
				warn("cannot stat 'vdb' or create '%s', huh?", buf);
			} else {
				/* for now we assume the VDB is a flat directory, e.g.
				 * there are no subdirs */
				for (vi = 0; vi < cnt; vi++) {
					if (move_file(src_fd, files[vi]->d_name,
							  	  dst_fd, files[vi]->d_name,
							  	  NULL) != 0)
						warn("failed to move 'vdb/%s' to '%s': %s",
							 files[vi]->d_name, buf, strerror(errno));
				}
				scandir_free(files, cnt);
			}
		}
	}

	/* clean up our local temp dir */
	xchdir("..");
	if (!keep_work)
		rm_rf(matom->PF);
	/* don't care about return, but when empty, remove */
	rmdir("../qmerge");

	printf("%s>>>%s %s\n",
			YELLOW, NORM, atom_format("%[CAT]%[PF]", matom));

	if (level == 0 && !pretend)
		qm_elog(" ::: completed emerge (%zu of %zu) %s to %s",
				qm_mg_total > 0 ? qm_mg_n : 1,
				qm_mg_total > 0 ? qm_mg_total : 1,
				atom_format("%[CAT]%[PF]", matom), portroot);
}

static int
pkg_unmerge(tree_pkg_ctx *pkg_ctx, depend_atom *rpkg, set *keep,
		int cp_argc, char **cp_argv, int cpm_argc, char **cpm_argv)
{
	atom_ctx *atom = tree_pkg_atom(pkg_ctx, false);
	char *phases;
	char *eprefix;
	size_t eprefix_len;
	char *contentsp;
	char *buf;
	char *savep;
	char T[_Q_PATH_MAX];
	int portroot_fd;
	llist_char *dirs = NULL;
	bool unmerge_config_protected;

	buf = phases = NULL;
	/* portage distinguishes explicit unmerges (one space, qlop -u)
	 * from autoclean-during-replace (two spaces, qlop -U) */
	if (!pretend)
		qm_elog(rpkg == NULL ? "=== Unmerging... (%s)"
							 : " === Unmerging... (%s)",
				atom_format("%[CAT]%[PF]", atom));
	snprintf(T, sizeof(T), "%s%s/qmerge._unmerge_.%s",
			 portroot, port_tmpdir, atom->PF);

	printf("%s***%s unmerging %s\n", YELLOW, NORM,
			atom_format("%[CATEGORY]%[PF]", atom));

	portroot_fd = tree_pkg_get_portroot_fd(pkg_ctx);

	/* execute the pkg_prerm step if we're just unmerging, not when
	 * replacing, pkg_merge will have called prerm right before merging
	 * the replacement package */
	if (!pretend && rpkg == NULL) {
		buf = tree_pkg_meta(pkg_ctx, Q_EAPI);
		if (buf == NULL)
			buf = (char *)"0";  /* default */
		phases = tree_pkg_meta(pkg_ctx, Q_DEFINED_PHASES);
		if (phases != NULL) {
			mkdir_p(T, 0755);
			pkg_run_func_at(portroot_fd, tree_pkg_get_path(pkg_ctx),
							phases, PKG_PRERM,
							T, T, buf, "");
		}
	}

	eprefix = tree_pkg_meta(pkg_ctx, Q_EPREFIX);
	if (eprefix == NULL)
		eprefix_len = 0;
	else
		eprefix_len = strlen(eprefix);

	unmerge_config_protected =
		contains_set("config-protect-if-modified", features);

	/* get a handle on the things to clean up */
	contentsp = tree_pkg_meta(pkg_ctx, Q_CONTENTS);
	if (contentsp == NULL)
		return 1;
	contentsp = xstrdup(contentsp);  /* should not modify pkg_ctx */

	for (buf = strtok_r(contentsp, "\n", &savep);
		 buf != NULL;
		 buf = strtok_r(NULL, "\n", &savep))
	{
		bool            del;
		contents_entry *e;
		char            zing[20];
		int             protected = 0;
		struct stat     st;

		e = contents_parse_line(buf);
		if (!e)
			continue;

		protected = config_protected(e->name + eprefix_len,
				cp_argc, cp_argv, cpm_argc, cpm_argv);

		/* This should never happen ... */
		assert(e->name[0] == '/' && e->name[1] != '/');

		/* Should we remove in order symlinks,objects,dirs ? */
		switch (e->type) {
			case CONTENTS_DIR: {
				/* since the dir contains files, we remove it later */
				llist_char *list = xmalloc(sizeof(llist_char));
				list->data = xstrdup(e->name);
				list->next = dirs;
				dirs = list;
				continue;
			}

			case CONTENTS_OBJ:
				if (protected && unmerge_config_protected) {
					/* If the file wasn't modified, unmerge it */
					char *hash = hash_file_at(portroot_fd,
							e->name + 1, HASH_MD5);
					protected = 0;
					if (hash != NULL)  /* if file was not removed */
						protected = strcmp(e->digest, (const char *)hash);
				}
				break;

			case CONTENTS_SYM:
				if (fstatat(portroot_fd,
							e->name + 1, &st, AT_SYMLINK_NOFOLLOW)) {
					if (errno != ENOENT) {
						warnp("stat failed for %s -> '%s'",
								e->name, e->sym_target);
						continue;
					} else
						break;
				}

				/* Hrm, if it isn't a symlink anymore, then leave it be */
				if (!S_ISLNK(st.st_mode))
					continue;

				break;

			default:
				warn("%s???%s %s%s%s (%d)", RED, NORM,
						WHITE, e->name, NORM, e->type);
				continue;
		}

		snprintf(zing, sizeof(zing), "%s%s%s",
				protected ? YELLOW : GREEN,
				protected ? "***" : "<<<" , NORM);

		if (protected) {
			qprintf("%s %s\n", zing, e->name);
			continue;
		}

		/* See if this file is owned by the incoming package (or by any
		 * other slot member being merged): if so, keep it.  Use a
		 * non-destructive membership test, del_set() would REMOVE the
		 * entry, so when collapsing several slot members the second
		 * unmerge would no longer see shared files in the keep set and
		 * would delete files the new package still owns. */
		del = false;
		if (keep != NULL)
			del = contains_set(e->name, keep) != NULL;
		if (del)
			strcpy(zing, "---");

		/* No match, so unmerge it */
		if (!quiet)
			printf("%s %s\n", zing, e->name);
		if (!keep || !del) {
			char *p;

			if (!pretend && unlinkat(portroot_fd, e->name + 1, 0)) {
				/* If a file was already deleted, ignore the error */
				if (errno != ENOENT)
					errp("could not unlink: %s%s", portroot, e->name + 1);
			}

			p = strrchr(e->name, '/');
			if (p) {
				*p = '\0';
				if (!pretend)
					rmdir_r_at(portroot_fd, e->name + 1);
			}
		}
	}

	free(contentsp);

	/* Then remove all dirs in reverse order */
	while (dirs != NULL) {
		llist_char *list;
		int rm;

		rm = pretend ? -1 : rmdir_r_at(portroot_fd, dirs->data + 1);
		qprintf("%s%s%s %s%s%s/\n", rm ? YELLOW : GREEN, rm ? "---" : "<<<",
			NORM, DKBLUE, dirs->data, NORM);

		list = dirs->next;
		free(dirs->data);
		free(dirs);
		dirs = list;
	}

	if (!pretend) {
		buf = tree_pkg_meta(pkg_ctx, Q_EAPI);
		if (buf == NULL)
			buf = (char *)"0";  /* default */
		phases = tree_pkg_meta(pkg_ctx, Q_DEFINED_PHASES);
		if (phases != NULL) {
			mkdir_p(T, 0755);
			/* execute the pkg_postrm step */
			pkg_run_func_at(portroot_fd, tree_pkg_get_path(pkg_ctx),
							phases, PKG_POSTRM,
							T, T, buf, rpkg == NULL ? "" : rpkg->PVR);
		}

		/* remove the tmp */
		rm_rf(T);
		rmdir(T);

		/* finally delete the vdb entry */
		rm_rf_at(portroot_fd, tree_pkg_get_path(pkg_ctx));
		unlinkat(portroot_fd, tree_pkg_get_path(pkg_ctx), AT_REMOVEDIR);

		/* and prune the category if it's empty */
		snprintf(T, sizeof(T), "%s", tree_pkg_get_path(pkg_ctx));
		contentsp = strrchr(T, '/');
		if (contentsp != NULL)
			*contentsp = '\0';
		unlinkat(portroot_fd, T, AT_REMOVEDIR);

		qm_elog(" >>> unmerge success: %s",
				atom_format("%[CAT]%[PF]", atom));
	}

	return 0;
}

static int
unlink_empty_at(int pfd, const char *buf)
{
	struct stat st;
	int fd;
	int ret = -1;

	fd = openat(pfd, buf, O_RDONLY);
	if (fd != -1 && stat(buf, &st) != -1) {
		if (st.st_size == 0)
			ret = unlinkat(pfd, buf, 0);
	}
	if (fd != -1)
		close(fd);
	return ret;
}

static int
pkg_verify_checksums(
		tree_pkg_ctx   *pkg,
		int             strict,
		int             display)
{
	atom_ctx *patom = tree_pkg_atom(pkg, false);
	char     *path  = tree_pkg_get_path(pkg);
	int       ret   = 0;
	char      md5[MD5_DIGEST_LENGTH + 1];
	char      sha1[SHA1_DIGEST_LENGTH + 1];
	char     *p;
	size_t    flen;
	int       mlen;
	bool      found = false;

	if (hash_multiple_file_at(tree_pkg_get_portroot_fd(pkg), path,
							  md5, sha1, NULL, NULL, NULL,
							  &flen, HASH_MD5 | HASH_SHA1) == -1)
		errf("failed to compute hashes for %s: %s\n",
				atom_to_string(patom), strerror(errno));

	if (display)
		printf("%s:\n", atom_to_string(patom));

	p = tree_pkg_meta(pkg, Q_SIZE);
	if (p != NULL)
		mlen = atoi(p);
	else
		mlen = 0;
	if (flen != (size_t)mlen) {
		warn("SIZE: [%sERR%s] %zu != %s for %s from %s\n",
			 RED, NORM, flen, p == NULL ? "?" : p, atom_to_string(patom), path);
		ret++;
	}
	else if (display)
	{
		printf("  SIZE: [%s;-)%s] %s\n", GREEN, NORM, p);
	}

	if ((p = tree_pkg_meta(pkg, Q_MD5)) != NULL) {
		if (strcmp(md5, p) == 0) {
			if (display)
				printf("  MD5:  [%s;-)%s] %s\n", GREEN, NORM, md5);
		} else {
			if (display)
				warn("    MD5:  [%sERR%s] (%s) != (%s) %s from %s",
					 RED, NORM, md5, p, atom_to_string(patom), path);
			ret++;
		}
		found = true;
	}

	if ((p = tree_pkg_meta(pkg, Q_SHA1)) != NULL) {
		if (strcmp(sha1, p) == 0) {
			if (display)
				qprintf("  SHA1: [%s;-)%s] %s\n", GREEN, NORM, sha1);
		} else {
			if (display)
				warn("   SHA1: [%sERR%s] (%s) != (%s) %s from %s",
					 RED, NORM, sha1, p, atom_to_string(patom), path);
			ret++;
		}
		found = true;
	}

	/* never return if we couldn't verify any hash */
	if (!found)
		return -1;

	if (strict && ret)
		errf("strict is set in features");

	return ret;
}

/* strip a binpkg store prefix from a tree-provided (portroot-relative)
 * binpkg path, returning the index-relative part */
static const char *
binpkg_relpath_loc(const char *path, const char *loc)
{
	const char *pd = loc;
	size_t      pdlen;

	while (*pd == '/')
		pd++;
	pdlen = strlen(pd);
	while (pdlen > 0 && pd[pdlen - 1] == '/')
		pdlen--;
	if (strncmp(path, pd, pdlen) == 0 && path[pdlen] == '/')
		path += pdlen + 1;
	return path;
}
#define binpkg_relpath(P) binpkg_relpath_loc(P, pkgdir)

/* inject()-alike: (re)generate PKGDIR/Packages from the binpkgs
 * found on disk, metadata read from the packages themselves
 * (xpak/gpkg), mirroring what `emaint binhost --fix` does */
struct qm_kv {
	const char *k;      /* name as written to the file */
	const char *sortk;  /* portage-internal name, used for ordering */
	char       *v;
};

static int
qm_kv_cmp(const void *a, const void *b)
{
	const struct qm_kv *x = a;
	const struct qm_kv *y = b;

	return strcmp(x->sortk, y->sortk);
}

static int
qm_strptr_cmp(const void *a, const void *b)
{
	return strcmp(*(char * const *)a, *(char * const *)b);
}

/* collapse all whitespace runs into single spaces and trim, the way
 * portage normalises values before writing them to Packages */
static char *
qm_ws_collapse(char *s)
{
	char *r = s;
	char *w = s;
	bool  sp = false;

	while (*r != '\0') {
		if (isspace((unsigned char)*r)) {
			sp = true;
			r++;
			continue;
		}
		if (sp && w != s)
			*w++ = ' ';
		sp = false;
		*w++ = *r++;
	}
	*w = '\0';
	return s;
}

static char *qm_set_join_sorted(set *s);

/* split a whitespace-separated value, dedupe and sort it, the way
 * portage normalises its incremental list variables; caller frees */
static char *
qm_split_sort_uniq(const char *v)
{
	set  *s;
	char *tmp;
	char *tok;
	char *sp;
	char *ret;

	if (v == NULL || v[0] == '\0')
		return NULL;
	s   = create_set();
	tmp = xstrdup(v);
	for (tok = strtok_r(tmp, " \t\n\\", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n\\", &sp))
	{
		/* incremental semantics, in order: -* clears, -x removes */
		if (tok[0] == '-') {
			if (tok[1] == '*' && tok[2] == '\0') {
				free_set(s);
				s = create_set();
			} else {
				bool rm;

				(void)del_set(tok + 1, s, &rm);
			}
			continue;
		}
		add_set_unique(tok, s, NULL);
	}
	free(tmp);
	ret = qm_set_join_sorted(s);
	free_set(s);
	return ret;
}

/* strip backslash-newline line continuations, keeping all other
 * characters verbatim (matches portage's evaluation of multi-line
 * quoted make.conf values); caller frees */
static char *
qm_strip_linecont(const char *v)
{
	char       *out;
	char       *w;
	const char *r;

	if (v == NULL || v[0] == '\0')
		return NULL;
	out = xstrdup(v);
	w   = out;
	for (r = v; *r != '\0'; r++) {
		/* a backslash, optionally followed by trailing whitespace,
		 * before a newline is a line continuation: drop it together
		 * with the newline (portage's reader joins such lines too,
		 * even where strict shell would not) */
		if (*r == '\\') {
			const char *la = r + 1;

			while (*la == ' ' || *la == '\t' || *la == '\r')
				la++;
			if (*la == '\n') {
				/* backslash [ws] newline: swallow up to and
				 * including the newline, keep the next indent */
				r = la;
				continue;
			}
			if (r[1] == ' ' || r[1] == '\t') {
				/* residue of an already-joined first line: the
				 * newline is gone, only drop the backslash */
				continue;
			}
		}
		*w++ = *r;
	}
	*w = '\0';
	return out;
}

/* look up a raw config variable (make.globals/profiles/make.conf) */
static const char *
qm_config_var(const char *name)
{
	const char *v = NULL;

	if (all_config_vars != NULL)
		v = get_set(name, all_config_vars);
	if (v == NULL)
		v = getenv(name);
	return v;
}

/* portage's settings[USE]: the globally effective USE consisting of
 * the incremental USE flags plus the expansion of every USE_EXPAND
 * variable (prefixed lowercase), unprefixed ones bare; sorted */
static char *
qm_effective_use(const char *use_expand_sorted,
				 const char *use_expand_unpref_sorted)
{
	/* NOTE: use_expand_sorted must be the union of USE_EXPAND and
	 * USE_EXPAND_IMPLICIT so that e.g. ARCH expands (bare) */
	set   *u = create_set();
	array *k;
	char  *flag;
	char  *ret;
	size_t i;

	if (ev_use != NULL) {
		k = set_keys(ev_use);
		array_for_each(k, i, flag)
			if (flag[0] != '-')
				add_set_unique(flag, u, NULL);
		array_free(k);
		/* apply negations the incremental way */
		k = set_keys(ev_use);
		array_for_each(k, i, flag)
			if (flag[0] == '-' && flag[1] != '*') {
				bool rm;

				(void)del_set(flag + 1, u, &rm);
			}
		array_free(k);
	}

	if (use_expand_sorted != NULL) {
		char *tmp = xstrdup(use_expand_sorted);
		char *var;
		char *sp;

		for (var = strtok_r(tmp, " ", &sp);
			 var != NULL;
			 var = strtok_r(NULL, " ", &sp))
		{
			const char *val = qm_config_var(var);
			char       *vtmp;
			char       *tok;
			char       *vsp;
			bool        unpref = false;

			if (val == NULL || val[0] == '\0')
				continue;
			if (use_expand_unpref_sorted != NULL) {
				char pat[128];
				char hay[512];

				snprintf(pat, sizeof(pat), " %s ", var);
				snprintf(hay, sizeof(hay), " %s ",
						 use_expand_unpref_sorted);
				unpref = strstr(hay, pat) != NULL;
			}

			vtmp = xstrdup(val);
			for (tok = strtok_r(vtmp, " \t\n\\", &vsp);
				 tok != NULL;
				 tok = strtok_r(NULL, " \t\n\\", &vsp))
			{
				char   buf[256];
				size_t vl = strlen(var);
				size_t bi;

				if (tok[0] == '-')
					continue;
				if (unpref) {
					add_set_unique(tok, u, NULL);
					continue;
				}
				snprintf(buf, sizeof(buf), "%s_%s", var, tok);
				for (bi = 0; bi < vl; bi++)
					buf[bi] = (char)tolower((unsigned char)buf[bi]);
				add_set_unique(buf, u, NULL);
			}
			free(vtmp);
		}
		free(tmp);
	}

	/* profile use.force adds, use.mask removes (mask wins), like
	 * portage's effective USE */
	if (use_force != NULL) {
		k = set_keys(use_force);
		array_for_each(k, i, flag)
			add_set_unique(flag, u, NULL);
		array_free(k);
	}
	if (use_mask != NULL) {
		k = set_keys(use_mask);
		array_for_each(k, i, flag) {
			bool rm;

			(void)del_set(flag, u, &rm);
		}
		array_free(k);
	}

	ret = qm_set_join_sorted(u);
	free_set(u);
	return ret;
}

/* space-join the members of a set in sorted order (for FEATURES/USE
 * header values); caller frees */
static char *
qm_set_join_sorted(set *s)
{
	array  *keys;
	char  **strs;
	char   *ret;
	char   *w;
	char   *k;
	size_t  cnt;
	size_t  i;
	size_t  len = 0;

	if (s == NULL)
		return NULL;
	keys = set_keys(s);
	cnt  = array_cnt(keys);
	if (cnt == 0) {
		array_free(keys);
		return NULL;
	}
	strs = xmalloc(sizeof(char *) * cnt);
	array_for_each(keys, i, k) {
		strs[i] = k;
		len += strlen(k) + 1;
	}
	qsort(strs, cnt, sizeof(char *), qm_strptr_cmp);
	ret = xmalloc(len + 1);
	w   = ret;
	for (i = 0; i < cnt; i++) {
		size_t l = strlen(strs[i]);

		if (i > 0)
			*w++ = ' ';
		memcpy(w, strs[i], l);
		w += l;
	}
	*w = '\0';
	free(strs);
	array_free(keys);
	return ret;
}

struct qm_idx_state {
	FILE   *fp;
	size_t  count;
	size_t  reused;
	set    *old;     /* relpath -> qm_oldblock, entries eligible for reuse */
	array  *entries; /* struct qm_entry, sorted before writing */
	array  *rrs;     /* struct qm_rr pairs seen in package metadata */
};

/* one finished index entry, kept for sorting */
struct qm_entry {
	atom_ctx *atom;
	char     *text;
};

/* a (repo, revision) pair from a package's REPO_REVISIONS */
struct qm_rr {
	char *name;
	char *rev;
};

/* portage's _cmp_cpv order: category, package, version, and for
 * multi-instance entries ascending BUILD_ID */
static int
qm_entry_cmp(const void *a, const void *b)
{
	const struct qm_entry *ea = *(const struct qm_entry * const *)a;
	const struct qm_entry *eb = *(const struct qm_entry * const *)b;
	int r;

	/* atom_compare only orders versions of the same package, so
	 * compare category/name explicitly first */
	r = strcmp(ea->atom->CATEGORY, eb->atom->CATEGORY);
	if (r != 0)
		return r;
	r = strcmp(ea->atom->PN, eb->atom->PN);
	if (r != 0)
		return r;
	r = atom_compare(ea->atom, eb->atom);
	if (r == OLDER)
		return -1;
	if (r == NEWER)
		return 1;
	return (int)ea->atom->BUILDID - (int)eb->atom->BUILDID;
}

/* a parsed entry from the previous index, reusable when the file's
 * mtime and size still match (same rule as emaint binhost --fix) */
struct qm_oldblock {
	long long mtime;
	long long size;
	char      raw[];   /* the entry block, verbatim */
};

/* parse the previous Packages file into relpath-keyed blocks; blocks
 * lacking PATH/MTIME/SIZE are simply not reusable and get recomputed */
static set *
binpkg_index_load_old(const char *file, array **blocks)
{
	char   *buf = NULL;
	size_t  len = 0;
	char   *blk;
	char   *end;
	set    *ret;

	if (!eat_file(file, &buf, &len) || buf == NULL) {
		free(buf);
		return NULL;
	}

	ret     = create_set();
	*blocks = array_new();

	/* skip the header block */
	blk = strstr(buf, "\n\n");
	if (blk == NULL) {
		free(buf);
		return ret;
	}
	blk += 2;

	while (*blk != '\0') {
		struct qm_oldblock *ob;
		char               *tmp;
		char               *line;
		char               *sp;
		char               *path = NULL;
		size_t              blen;

		end = strstr(blk, "\n\n");
		if (end == NULL)
			end = blk + strlen(blk);
		else
			end += 1;   /* keep the final newline of the block */

		blen = (size_t)(end - blk);
		ob = xmalloc(sizeof(*ob) + blen + 1);
		memcpy(ob->raw, blk, blen);
		ob->raw[blen] = '\0';
		ob->mtime = -1;
		ob->size  = -1;

		tmp = xstrdup(ob->raw);
		for (line = strtok_r(tmp, "\n", &sp);
			 line != NULL;
			 line = strtok_r(NULL, "\n", &sp))
		{
			if (strncmp(line, "PATH: ", 6) == 0 && path == NULL)
				path = xstrdup(line + 6);
			else if (strncmp(line, "MTIME: ", 7) == 0)
				ob->mtime = atoll(line + 7);
			else if (strncmp(line, "SIZE: ", 6) == 0)
				ob->size = atoll(line + 6);
		}
		free(tmp);

		if (path != NULL && ob->mtime >= 0 && ob->size >= 0) {
			void *prev = NULL;
			add_set_value(path, ob, &prev, ret);
			array_append(*blocks, ob);
		} else {
			free(ob);
		}
		free(path);

		while (*end == '\n')
			end++;
		blk = end;
	}

	free(buf);
	return ret;
}

static int
binpkg_index_cb(tree_pkg_ctx *pkg, void *priv)
{
	struct qm_idx_state *st   = priv;
	atom_ctx            *atom = tree_pkg_atom(pkg, false);
	char                 md5[MD5_DIGEST_LENGTH + 1];
	char                 sha1[SHA1_DIGEST_LENGTH + 1];
	size_t               flen;
	size_t               i;
	size_t               nkv;
	struct qm_kv         kv[40];
	struct qm_entry     *ent;
	char                *v;
	FILE                *ms;
	char                *mstxt = NULL;
	size_t               mslen = 0;
	static const struct {
		enum tree_pkg_meta_keys key;
		const char             *name;
	} keys[] = {
		{ Q_BDEPEND,        "BDEPEND"        },
		{ Q_BUILD_TIME,     "BUILD_TIME"     },
		{ Q_CHOST,          "CHOST"          },
		{ Q_DEFINED_PHASES, "DEFINED_PHASES" },
		{ Q_DEPEND,         "DEPEND"         },
		{ Q_EAPI,           "EAPI"           },
		{ Q_IDEPEND,        "IDEPEND"        },
		{ Q_IUSE,           "IUSE"           },
		{ Q_KEYWORDS,       "KEYWORDS"       },
		{ Q_LICENSE,        "LICENSE"        },
		{ Q_PDEPEND,        "PDEPEND"        },
		{ Q_PROPERTIES,     "PROPERTIES"     },
		{ Q_PROVIDES,       "PROVIDES"       },
		{ Q_RDEPEND,        "RDEPEND"        },
		{ Q_repository,     "REPO"           },
		{ Q_REQUIRES,       "REQUIRES"       },
		{ Q_RESTRICT,       "RESTRICT"       },
		{ Q_SLOT,           "SLOT"           },
		{ Q_USE,            "USE"            },
	};
	const char *relpath = binpkg_relpath(tree_pkg_get_path(pkg));
	struct stat stt;

	if (fstatat(tree_pkg_get_portroot_fd(pkg),
				tree_pkg_get_path(pkg), &stt, 0) != 0)
	{
		warn("index: skipping %s: cannot stat %s",
			 atom_to_string(atom), tree_pkg_get_path(pkg));
		return 0;
	}

	/* incremental: reuse the previous entry when the file has not
	 * changed, avoiding rehash and metadata extraction */
	if (st->old != NULL) {
		struct qm_oldblock *ob =
			(struct qm_oldblock *)get_set(relpath, st->old);

		if (ob != NULL &&
				ob->mtime == (long long)stt.st_mtime &&
				ob->size  == (long long)stt.st_size)
		{
			ent = xzalloc(sizeof(*ent));
			ent->atom = atom;
			ent->text = xstrdup(ob->raw);
			if (st->entries == NULL)
				st->entries = array_new();
			array_append(st->entries, ent);
			st->count++;
			st->reused++;
			return 0;
		}
	}

	if (hash_multiple_file_at(tree_pkg_get_portroot_fd(pkg),
							  tree_pkg_get_path(pkg),
							  md5, sha1, NULL, NULL, NULL,
							  &flen, HASH_MD5 | HASH_SHA1) == -1)
	{
		warn("index: skipping %s: cannot hash %s",
			 atom_to_string(atom), tree_pkg_get_path(pkg));
		return 0;
	}

	nkv = 0;
#define QM_KVF(K, SK, ...) \
	do { \
		xasprintf(&kv[nkv].v, __VA_ARGS__); \
		kv[nkv].k = K; \
		kv[nkv].sortk = SK; \
		nkv++; \
	} while (0)

	QM_KVF("CPV", "CPV", "%s/%s", atom->CATEGORY, atom->PF);
	/* portage takes BUILD_ID from the package metadata (which for
	 * quickpkg'd instances is the installed build), falling back to
	 * the filename-derived instance number */
	v = tree_pkg_meta(pkg, Q_BUILD_ID);
	if (v != NULL && v[0] != '\0')
		QM_KVF("BUILD_ID", "BUILD_ID", "%s", v);
	else if (atom->BUILDID > 0)
		QM_KVF("BUILD_ID", "BUILD_ID", "%u", atom->BUILDID);
	QM_KVF("MD5", "MD5", "%s", md5);
	QM_KVF("SHA1", "SHA1", "%s", sha1);
	/* portage sorts on its internal key names: _mtime_ and
	 * repository (lowercase) order after all uppercase keys */
	QM_KVF("MTIME", "_mtime_", "%lld", (long long)stt.st_mtime);
	QM_KVF("SIZE", "SIZE", "%zu", flen);
	QM_KVF("PATH", "PATH", "%s", relpath);
#undef QM_KVF

	for (i = 0; i < ARRAY_SIZE(keys); i++) {
		v = tree_pkg_meta(pkg, keys[i].key);
		if (v == NULL || v[0] == '\0')
			continue;
		v = qm_ws_collapse(xstrdup(v));
		/* portage's index compression: omit values matching the
		 * well-known defaults, and CHOST when equal to the header */
		if (v[0] == '\0' ||
				(keys[i].key == Q_EAPI && strcmp(v, "0") == 0) ||
				(keys[i].key == Q_SLOT && strcmp(v, "0") == 0) ||
				(keys[i].key == Q_CHOST &&
				 chost[0] != '\0' && strcmp(v, chost) == 0))
		{
			free(v);
			continue;
		}
		kv[nkv].k     = keys[i].name;
		kv[nkv].sortk = keys[i].key == Q_repository ?
				"repository" : keys[i].name;
		kv[nkv].v     = v;
		nkv++;
	}

	/* REPO_REVISIONS is not written per entry (emaint drops it), but
	 * the pairs feed the forward-progress header value */
	v = tree_pkg_meta(pkg, Q_REPO_REVISIONS);
	if (v != NULL) {
		const char *p = v;

		while ((p = strchr(p, '"')) != NULL) {
			const char *ne = strchr(p + 1, '"');
			const char *rs;
			const char *re;

			if (ne == NULL)
				break;
			rs = strchr(ne + 1, '"');
			if (rs == NULL)
				break;
			re = strchr(rs + 1, '"');
			if (re == NULL)
				break;
			{
				struct qm_rr *rr = xzalloc(sizeof(*rr));

				rr->name = xstrdup("");
				free(rr->name);
				rr->name = xmalloc((size_t)(ne - p));
				memcpy(rr->name, p + 1, (size_t)(ne - p - 1));
				rr->name[ne - p - 1] = '\0';
				rr->rev = xmalloc((size_t)(re - rs));
				memcpy(rr->rev, rs + 1, (size_t)(re - rs - 1));
				rr->rev[re - rs - 1] = '\0';
				if (st->rrs == NULL)
					st->rrs = array_new();
				array_append(st->rrs, rr);
			}
			p = re + 1;
		}
	}

	/* render the entry into memory, fields sorted the portage way */
	ms = open_memstream(&mstxt, &mslen);
	if (ms == NULL)
		err("open_memstream failed");
	qsort(kv, nkv, sizeof(*kv), qm_kv_cmp);
	for (i = 0; i < nkv; i++) {
		fprintf(ms, "%s: %s\n", kv[i].k, kv[i].v);
		free(kv[i].v);
	}
	fclose(ms);

	ent = xzalloc(sizeof(*ent));
	ent->atom = atom;
	ent->text = mstxt;
	if (st->entries == NULL)
		st->entries = array_new();
	array_append(st->entries, ent);
	st->count++;
	return 0;
}

static int
binpkg_index_regen(void)
{
	struct qm_idx_state st;
	tree_ctx           *bin;
	FILE               *out;
	FILE               *body;
	int                 ret;
	char                pdir[_Q_PATH_MAX];
	char                finp[_Q_PATH_MAX + 16];
	char                oldp[_Q_PATH_MAX + 32];
	char                newp[_Q_PATH_MAX + 32];
	char                buf[BUFSIZ];
	size_t              n;
	bool                hadold;
	set                *oldset;
	array              *oldmem;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	snprintf(finp, sizeof(finp), "%s/%s", pdir, Packages);
	snprintf(oldp, sizeof(oldp), "%s.regen-old", finp);
	snprintf(newp, sizeof(newp), "%s.regen-new", finp);

	/* incremental by default: parse the previous index so unchanged
	 * packages keep their entries verbatim; -F forces a full rebuild */
	oldmem = NULL;
	oldset = force_download != 0 ? NULL :
			 binpkg_index_load_old(finp, &oldmem);

	/* move a pre-existing index out of the way, so the tree layer
	 * dir-scans the actual binpkgs instead of trusting the index;
	 * it is restored when anything below fails */
	hadold = rename(finp, oldp) == 0;

	st.fp      = NULL;
	st.count   = 0;
	st.reused  = 0;
	st.old     = oldset;
	st.entries = NULL;
	st.rrs     = NULL;
	bin = tree_new(portroot, pkgdir, TREETYPE_BINPKG, false);
	if (bin == NULL) {
		warn("cannot open %s", pdir);
		goto fail;
	}

	st.fp = fopen(newp, "w");
	if (st.fp == NULL) {
		warnp("cannot open %s for writing", newp);
		tree_close(bin);
		goto fail;
	}

	tree_foreach_pkg_sorted(bin, binpkg_index_cb, &st, NULL);

	/* write the entries in portage's order */
	if (st.entries != NULL) {
		size_t            ecnt = array_cnt(st.entries);
		size_t            ei;
		struct qm_entry  *e;
		struct qm_entry **list = xmalloc(sizeof(*list) * (ecnt + 1));

		array_for_each(st.entries, ei, e)
			list[ei] = e;
		qsort(list, ecnt, sizeof(*list), qm_entry_cmp);
		for (ei = 0; ei < ecnt; ei++) {
			fputs(list[ei]->text, st.fp);
			fputc('\n', st.fp);
		}
		free(list);
	}
	fclose(st.fp);
	tree_close(bin);

	/* final index = header + body */
	out = fopen(finp, "w");
	if (out == NULL) {
		warnp("cannot open %s for writing", finp);
		goto fail;
	}
	/* portage-parity header: sorted key: value lines of the relevant
	 * build-host configuration (cf. bintree._update_pkgindex_header) */
	{
		struct qm_kv hdr[48];
		size_t       nh = 0;
		size_t       hi;
		char         pkgsbuf[32];
		char         tsbuf[32];
		char         profbuf[_Q_PATH_MAX];
		char        *featstr;
		char        *usestr;
		char        *ue_sorted;
		char        *ueh_sorted;
		char        *uei_sorted;
		char        *ueu_sorted;
		char        *iuseimp_sorted;
		char        *cp_sorted;
		char        *cpm_sorted;
		char        *im_sorted;
		char        *mirrors;
		char        *dynkeys[16];
		char        *dynvals[16];
		size_t       ndyn = 0;

#define QM_HV(K, V) \
		do { \
			if ((V) != NULL && (V)[0] != '\0') { \
				hdr[nh].k     = K; \
				hdr[nh].sortk = K; \
				hdr[nh].v     = (char *)(V); \
				nh++; \
			} \
		} while (0)

		featstr        = qm_set_join_sorted(features);
		ue_sorted      = qm_split_sort_uniq(use_expand);
		ueh_sorted     = qm_split_sort_uniq(use_expand_hidden);
		uei_sorted     = qm_split_sort_uniq(use_expand_implicit);
		ueu_sorted     = qm_split_sort_uniq(use_expand_unprefixed);
		iuseimp_sorted = qm_split_sort_uniq(iuse_implicit);
		cp_sorted      = qm_split_sort_uniq(config_protect);
		cpm_sorted     = qm_split_sort_uniq(config_protect_mask);
		{
			const char *im_raw = qm_config_var("INSTALL_MASK");

			im_sorted = qm_strip_linecont(
					im_raw != NULL ? im_raw : install_mask);
		}
		mirrors        = qm_strip_linecont(gentoo_mirrors);
		{
			char *uni = NULL;

			xasprintf(&uni, "%s %s",
					  use_expand != NULL ? use_expand : "",
					  use_expand_implicit != NULL ?
							use_expand_implicit : "");
			usestr = NULL;
			{
				char *uni_sorted = qm_split_sort_uniq(uni);

				usestr = qm_effective_use(uni_sorted, ueu_sorted);
				free(uni_sorted);
			}
			free(uni);
		}

		QM_HV("ACCEPT_KEYWORDS",       accept_keywords);
		QM_HV("ACCEPT_LICENSE",        accept_license);
		QM_HV("ACCEPT_PROPERTIES",     accept_properties);
		QM_HV("ACCEPT_RESTRICT",       accept_restrict);
		QM_HV("CBUILD", cbuild[0] != '\0' ? cbuild : chost);
		QM_HV("CHOST",                 chost);
		QM_HV("CONFIG_PROTECT",        cp_sorted);
		QM_HV("CONFIG_PROTECT_MASK",   cpm_sorted);
		QM_HV("FEATURES",              featstr);
		QM_HV("GENTOO_MIRRORS",        mirrors);
		QM_HV("INSTALL_MASK",          im_sorted);
		QM_HV("IUSE_IMPLICIT",         iuseimp_sorted);
		QM_HV("USE",                   usestr);
		QM_HV("USE_EXPAND",            ue_sorted);
		QM_HV("USE_EXPAND_HIDDEN",     ueh_sorted);
		QM_HV("USE_EXPAND_IMPLICIT",   uei_sorted);
		QM_HV("USE_EXPAND_UNPREFIXED", ueu_sorted);

		/* current values of USE_EXPAND_IMPLICIT members that are not
		 * unprefixed, plus their USE_EXPAND_VALUES_* lists, so the
		 * binhost is usable without a local profile (bug #470006) */
		if (uei_sorted != NULL) {
			char *toks = xstrdup(uei_sorted);
			char *tok;
			char *sp;

			for (tok = strtok_r(toks, " ", &sp);
				 tok != NULL && ndyn + 2 <= ARRAY_SIZE(dynkeys);
				 tok = strtok_r(NULL, " ", &sp))
			{
				const char *tval;
				char        vname[160];
				bool        unpref = false;

				if (ueu_sorted != NULL) {
					char pat[128];
					char hay[512];

					snprintf(pat, sizeof(pat), " %s ", tok);
					snprintf(hay, sizeof(hay), " %s ", ueu_sorted);
					unpref = strstr(hay, pat) != NULL;
				}

				(void)unpref;
				tval = strcmp(tok, "ARCH") == 0 ?
						portarch : qm_config_var(tok);
				if (tval != NULL && tval[0] != '\0') {
					dynkeys[ndyn] = xstrdup(tok);
					dynvals[ndyn] = xstrdup(tval);
					QM_HV(dynkeys[ndyn], dynvals[ndyn]);
					ndyn++;
				}

				snprintf(vname, sizeof(vname),
						 "USE_EXPAND_VALUES_%s", tok);
				tval = qm_config_var(vname);
				if (tval != NULL && tval[0] != '\0') {
					dynkeys[ndyn] = xstrdup(vname);
					dynvals[ndyn] = xstrdup(tval);
					QM_HV(dynkeys[ndyn], dynvals[ndyn]);
					ndyn++;
				}
			}
			free(toks);
		}

		/* PROFILE: the make.profile target relative to profiles/ */
		profbuf[0] = '\0';
		{
			char  lnk[_Q_PATH_MAX];
			char  rl[_Q_PATH_MAX];
			char *pp;

			snprintf(lnk, sizeof(lnk), "%s/etc/portage/make.profile",
					 configroot);
			if (realpath(lnk, rl) == NULL) {
				snprintf(lnk, sizeof(lnk), "%s/etc/make.profile",
						 configroot);
				if (realpath(lnk, rl) == NULL)
					rl[0] = '\0';
			}
			/* like portage: strip only when the profile lives under
			 * $PORTDIR/profiles/, else record the full path */
			pp = NULL;
			if (rl[0] != '\0' && main_overlay != NULL) {
				char pbase[_Q_PATH_MAX];

				if (realpath(main_overlay, pbase) != NULL) {
					size_t pblen = strlen(pbase);

					if (strncmp(rl, pbase, pblen) == 0 &&
							strncmp(rl + pblen, "/profiles/",
									sizeof("/profiles/") - 1) == 0)
						pp = rl + pblen +
								sizeof("/profiles/") - 1;
				}
			}
			if (pp != NULL)
				snprintf(profbuf, sizeof(profbuf), "%s", pp);
			else if (rl[0] != '\0')
				snprintf(profbuf, sizeof(profbuf), "%s", rl);
		}
		QM_HV("PROFILE", profbuf);

		/* binhost servers advertise their canonical base URI and
		 * cache TTL (cf. bintree._update_pkgindex_header) */
		QM_HV("URI", qm_config_var("PORTAGE_BINHOST_HEADER_URI"));
		QM_HV("TTL", qm_config_var("PORTAGE_BINHOST_TTL"));

		snprintf(pkgsbuf, sizeof(pkgsbuf), "%zu", st.count);
		QM_HV("PACKAGES", pkgsbuf);
		snprintf(tsbuf, sizeof(tsbuf), "%zu", (size_t)time(NULL));
		QM_HV("TIMESTAMP", tsbuf);
		QM_HV("VERSION", "0");
#undef QM_HV

		qsort(hdr, nh, sizeof(*hdr), qm_kv_cmp);
		for (hi = 0; hi < nh; hi++) {
			const char *c;

			fprintf(out, "%s: ", hdr[hi].k);
			/* like portage's index writer: embedded newlines
			 * become single spaces, all other spacing verbatim */
			for (c = hdr[hi].v; *c != '\0'; c++)
				fputc(*c == '\n' || *c == '\r' ? ' ' : *c, out);
			fputc('\n', out);
		}
		fputc('\n', out);

		free(featstr);
		free(usestr);
		free(ue_sorted);
		free(ueh_sorted);
		free(uei_sorted);
		free(ueu_sorted);
		free(iuseimp_sorted);
		free(cp_sorted);
		free(cpm_sorted);
		free(im_sorted);
		free(mirrors);
		for (hi = 0; hi < ndyn; hi++) {
			free(dynkeys[hi]);
			free(dynvals[hi]);
		}
	}
	body = fopen(newp, "r");
	if (body != NULL) {
		while ((n = fread(buf, 1, sizeof(buf), body)) > 0)
			fwrite(buf, 1, n, out);
		fclose(body);
	}
	fclose(out);
	unlink(newp);
	if (hadold)
		unlink(oldp);
	binpkg_perms(finp, false);

	/* FEATURES=compress-index: maintain the Packages.gz twin the way
	 * portage does, from the exact same content */
	{
		char gzp[_Q_PATH_MAX + 32];

		snprintf(gzp, sizeof(gzp), "%s.gz", finp);
		if (contains_set("compress-index", features)) {
			FILE   *fin = fopen(finp, "r");
			gzFile  gz  = gzopen(gzp, "wb9");

			if (fin != NULL && gz != NULL) {
				char   gbuf[BUFSIZ];
				size_t gn;

				while ((gn = fread(gbuf, 1, sizeof(gbuf), fin)) > 0)
					gzwrite(gz, gbuf, (unsigned)gn);
			}
			if (gz != NULL)
				gzclose(gz);
			if (fin != NULL)
				fclose(fin);
			binpkg_perms(gzp, false);
		} else {
			unlink(gzp);   /* no stale compressed twin */
		}
	}

	/* package-moves + news transports for repo-less consumers */
	qm_emit_moves(pdir);
	qm_emit_news(pdir);

	qprintf("%s>>>%s indexed %zu binpkg%s (%zu reused) in %s\n",
			GREEN, NORM, st.count, st.count == 1 ? "" : "s",
			st.reused, pdir);
	ret = EXIT_SUCCESS;
	goto out;

 fail:
	unlink(newp);
	if (hadold && rename(oldp, finp) != 0)
		warnp("failed to restore previous %s", finp);
	ret = EXIT_FAILURE;

 out:
	if (st.entries != NULL) {
		size_t           ei;
		struct qm_entry *e;

		array_for_each(st.entries, ei, e) {
			free(e->text);
			free(e);
		}
		array_free(st.entries);
	}
	if (st.rrs != NULL) {
		size_t        ri;
		struct qm_rr *rr;

		array_for_each(st.rrs, ri, rr) {
			free(rr->name);
			free(rr->rev);
			free(rr);
		}
		array_free(st.rrs);
	}
	if (oldmem != NULL) {
		struct qm_oldblock *ob;
		size_t              bi;

		array_for_each(oldmem, bi, ob)
			free(ob);
		array_free(oldmem);
	}
	if (oldset != NULL)
		free_set(oldset);
	return ret;
}

/* Download mpkg's binary package into PKGDIR if it is not already present.
 * This is the network-bound half of pkg_fetch and is safe to run in a
 * forked worker: it only ever writes the package's own gpkg file (a
 * distinct path per package) and touches no VDB or shared mutable state.
 * Returns true iff the package file is available in PKGDIR afterwards. */
static bool
pkg_download(tree_pkg_ctx *mpkg)
{
	atom_ctx   *patom   = tree_pkg_atom(mpkg, false);
	ssize_t     repoidx = qm_repoidx_of_pkg(mpkg);
	char        locbuf[_Q_PATH_MAX];
	const char *loc     = repoidx >= 0 && qm_nbinrepos > 0 ?
			qm_repo_loc((size_t)repoidx, locbuf, sizeof(locbuf)) : pkgdir;

	unlink_empty_at(tree_pkg_get_portroot_fd(mpkg), tree_pkg_get_path(mpkg));

	if (mkdir_p_at(tree_pkg_get_portroot_fd(mpkg), loc + 1, 0755) == -1)
	{
		warn("Failed to create %s", loc);
		return false;
	}

	if (force_download &&
		faccessat(tree_pkg_get_portroot_fd(mpkg),
				  tree_pkg_get_path(mpkg), R_OK, 0) == 0)
	{
		if (getenv("QMERGE_REFETCH") != NULL) {
			/* force re-download: drop the cached gpkg WITHOUT verifying it,
			 * so the fetch below pulls a fresh copy regardless of cache. */
			if (getenv("QMERGE") == NULL)
				unlinkat(tree_pkg_get_portroot_fd(mpkg),
						 tree_pkg_get_path(mpkg), 0);
		} else if (pkg_verify_checksums(mpkg, 0, 0) != 0) {
			if (getenv("QMERGE") == NULL)
				unlinkat(tree_pkg_get_portroot_fd(mpkg),
						 tree_pkg_get_path(mpkg), 0);
		} else if (!quiet) {
			/* present and checksum-valid: reused, NOT re-downloaded.  Emit
			 * a per-package line anyway so a full-cache -f shows steady
			 * progress (the re-verify is slow, GB-scale I/O) instead of
			 * looking hung, and clearly labels it [cached] so it can't be
			 * mistaken for a re-download. */
			if (qm_dl_total > 0)
				printf(">>> (%zu of %zu) %s [cached]\n",
						qm_dl_n, qm_dl_total, atom_to_string(patom));
			else
				printf(">>> %s [cached]\n", atom_to_string(patom));
			fflush(stdout);
		}
	}

	if (faccessat(tree_pkg_get_portroot_fd(mpkg),
				  tree_pkg_get_path(mpkg), R_OK, 0) != 0)
	{
		char *p;
		char  dest[_Q_PATH_MAX];

		/* only reached when the gpkg is genuinely absent (or was dropped
		 * by -f for a bad checksum), so this line marks a REAL download --
		 * a repeat -f over a valid cache prints nothing here.  -q silences
		 * it; the (N of M) counter comes from the prefetch pool. */
		if (!quiet) {
			if (qm_dl_total > 0)
				printf(">>> Fetching (%zu of %zu) %s\n",
						qm_dl_n, qm_dl_total, atom_to_string(patom));
			else
				printf(">>> Fetching %s\n", atom_to_string(patom));
			fflush(stdout);
		}

		/* tree_pkg_meta(Q_PATH) hands back the full local path
		 * (pkgdir-prefixed, see tree.c); recover the index-relative
		 * part, which is both the remote URL path and the layout to
		 * mirror below PKGDIR (multi-instance binhosts use
		 * CAT/PN/PF-BUILDID.gpkg.tar with a PN subdirectory) */
		p = tree_pkg_meta(mpkg, Q_PATH);
		if (p == NULL) {
			warn("missing PATH in binpkg index for %s, skipping",
				 atom_to_string(patom));
			return false;
		}

		p = (char *)binpkg_relpath_loc(p, loc);
		{
			const char *sl   = strrchr(p, '/');
			int         plen = sl == NULL ? 0 : (int)(sl - p);

			if ((size_t)snprintf(dest, sizeof(dest), "%s%s%s%.*s",
								 portroot, loc,
								 plen > 0 ? "/" : "", plen, p)
					>= sizeof(dest))
			{
				warn("binpkg path too long for %s, skipping",
					 atom_to_string(patom));
				return false;
			}
		}
		if (mkdir_p(dest, 0755) != 0)
		{
			warnp("Failed to create %s", dest);
			return false;
		}
		binpkg_tree_perms(dest);

		/* route to the repo that advertised this pkg; only when that
		 * fails walk the full fallback order */
		if (repoidx < 0 || fetch_repo((size_t)repoidx, dest, p) != 0)
			fetch(dest, p);

		/* verify the pkg exists now. unlink if zero bytes */
		unlink_empty_at(tree_pkg_get_portroot_fd(mpkg),
						tree_pkg_get_path(mpkg));
	}

	if (faccessat(tree_pkg_get_portroot_fd(mpkg),
				  tree_pkg_get_path(mpkg), R_OK, 0) != 0)
	{
		warn("Failed to fetch %s from any configured binhost", patom->PF);
		fflush(stderr);
		return false;
	}

	return true;
}

static void
pkg_fetch(int level, const depend_atom *qatom, tree_pkg_ctx *mpkg)
{
	atom_ctx *patom     = tree_pkg_atom(mpkg, false);
	int       verifyret;
	char      pkg_key[512];

	/* remember CATEGORY/PF of everything queued in this run, so
	 * cyclic or duplicate dependencies are processed only once */
	snprintf(pkg_key, sizeof(pkg_key), "%s/%s",
			 patom->CATEGORY != NULL ? patom->CATEGORY : "",
			 patom->PF != NULL ? patom->PF : "");
	if (_qmerge_processed_pkgs != NULL &&
			contains_set(pkg_key, _qmerge_processed_pkgs) != NULL) {
		IF_DEBUG(fprintf(stderr, "  skipping already queued %s\n", pkg_key));
		return;
	}
	if (_qmerge_processed_pkgs == NULL)
		_qmerge_processed_pkgs = create_set();
	add_set(pkg_key, _qmerge_processed_pkgs);

	/* package.mask visibility gate (backstop; selection already filters) */
	if (binpkg_masked(patom)) {
		warn("%s is masked by package.mask -- refusing (unmask to override)",
			 atom_to_string(patom));
		return;
	}

	/* GLEP 53: keyword visibility gate, before fetching or merging */
	if (!binpkg_keywords_ok(mpkg, patom, false))
		return;

	/* GLEP 23: license visibility gate */
	if (!binpkg_license_ok(mpkg, patom, false))
		return;

	/* --usepkg-exclude backstop (selection already filters) */
	if (binpkg_excluded(mpkg, patom, false))
		return;

	/* qmerge -pv patch */
	if (pretend) {
		if (!install)
			install++;
		pkg_merge(level, qatom, mpkg);
		return;
	}

	/* download into PKGDIR (a no-op when a parallel prefetch already
	 * pulled it, or when the package is otherwise present) */
	if (!pkg_download(mpkg))
		return;

	/* check to see if checksum matches */
	verifyret = pkg_verify_checksums(mpkg, qmerge_strict, !quiet);
	if (verifyret == -1) {
		warn("No checksum data for %s (try `emaint binhost --fix`)",
				tree_pkg_get_path(mpkg));
		return;
	} else if (verifyret == 0) {
		pkg_merge(0, qatom, mpkg);
		return;
	}
}

/* Workaround: pull this in, knowing that qlist will be in the final link, we
 * should however figure out how to do what match does here from e.g.
 * atom   FIXME use tree_match_atom instead */
extern bool qlist_match(
		tree_pkg_ctx *pkg_ctx,
		const char *name,
		depend_atom **name_atom,
		bool exact,
		bool applymasks);

/* collect the CONTENTS file/symlink paths of one installed package into
 * the keep set, unless it is the package we are about to unmerge */
struct qm_keepscan {
	set        *keep;
	const char *skip_cat;
	const char *skip_pf;
};

static int
qm_keepscan_cb(tree_pkg_ctx *pkg_ctx, void *priv)
{
	struct qm_keepscan *ks = priv;
	atom_ctx           *a  = tree_pkg_atom(pkg_ctx, false);
	char               *contents;
	char               *line;
	char               *savep;

	if (a != NULL && a->CATEGORY != NULL && a->PF != NULL &&
			strcmp(a->CATEGORY, ks->skip_cat) == 0 &&
			strcmp(a->PF, ks->skip_pf) == 0)
		return 0;  /* the package being unmerged: its files are fair game */

	contents = tree_pkg_meta(pkg_ctx, Q_CONTENTS);
	if (contents == NULL)
		return 0;
	contents = xstrdup(contents);  /* contents_parse_line mutates the buf */

	for (line = strtok_r(contents, "\n", &savep);
			line != NULL;
			line = strtok_r(NULL, "\n", &savep))
	{
		contents_entry *e = contents_parse_line(line);
		if (e != NULL && (e->type == CONTENTS_OBJ || e->type == CONTENTS_SYM))
			add_set(e->name, ks->keep);
	}

	free(contents);
	return 0;
}

/* Build the set of all regular-file/symlink paths owned by installed
 * packages OTHER than skip_cat/skip_pf.  Passed to pkg_unmerge as its
 * keep set so a standalone unmerge never deletes a file another package
 * still owns, Portage gives the same protection via others_in_slot. */
static set *
qm_other_owned_files(const char *skip_cat, const char *skip_pf)
{
	struct qm_keepscan ks;
	tree_ctx          *vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);

	ks.keep     = create_set();
	ks.skip_cat = skip_cat;
	ks.skip_pf  = skip_pf;

	if (vdb != NULL) {
		tree_foreach_pkg_fast(vdb, qm_keepscan_cb, &ks, NULL);
		tree_close(vdb);
	}

	return ks.keep;
}

static int
qmerge_unmerge_cb(tree_pkg_ctx *pkg_ctx, void *priv)
{
	int cp_argc;
	int cpm_argc;
	char **cp_argv;
	char **cpm_argv;
	char *p;
	array *todo;
	size_t n;

	makeargv(config_protect, &cp_argc, &cp_argv);
	makeargv(config_protect_mask, &cpm_argc, &cpm_argv);

	todo = set_keys(priv);
	array_for_each(todo, n, p)
	{
		if (qlist_match(pkg_ctx, p, NULL, true, false)) {
			atom_ctx *a    = tree_pkg_atom(pkg_ctx, false);
			set      *keep = uninstall_force
					? create_set()
					: qm_other_owned_files(a->CATEGORY, a->PF);
			pkg_unmerge(pkg_ctx, NULL, keep,
					cp_argc, cp_argv, cpm_argc, cpm_argv);
			free_set(keep);
		}
	}
	array_free(todo);

	freeargv(cp_argc, cp_argv);
	freeargv(cpm_argc, cpm_argv);

	return 0;
}

static int
unmerge_packages(set *todo)
{
	tree_ctx *vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);
	int ret = 1;
	if (vdb != NULL) {
		ret = tree_foreach_pkg_fast(vdb, qmerge_unmerge_cb, todo, NULL);
		tree_close(vdb);
	}
	return ret;
}

static set *
qmerge_add_set_file(const char *pfx, const char *dir, const char *file, set *q)
{
	FILE *fp;
	int linelen;
	size_t buflen;
	char *buf, *fname;

	/* Find the file to read */
	xasprintf(&fname, "%s%s%s/%s", portroot, pfx, dir, file);

	if ((fp = fopen(fname, "r")) == NULL) {
		warnp("unable to read set file %s", fname);
		free(fname);
		return NULL;
	}
	free(fname);

	/* Load each entry */
	buf = NULL;
	while ((linelen = getline(&buf, &buflen, fp)) >= 0) {
		rmspace_len(buf, (size_t)linelen);
		q = add_set_unique(buf, q, NULL);
	}
	free(buf);

	fclose(fp);

	return q;
}

static void *
qmerge_add_set_system(void *data, char *buf)
{
	set *q = data;
	char *s;

	s = strchr(buf, '#');
	if (s)
		*s = '\0';
	rmspace(buf);

	s = buf;
	if (*s == '*')
		q = add_set(s + 1, q);
	else if (s[0] == '-' && s[1] == '*') {
		bool ok;
		(void)del_set(s + 2, q, &ok);
	}

	return q;
}

static int
qmerge_all_cb(tree_pkg_ctx *pkg, void *priv)
{
	set     **q = priv;
	atom_ctx *a = tree_pkg_atom(pkg, false);
	char      cpn[512];

	if (a == NULL || a->CATEGORY == NULL || a->PN == NULL)
		return 0;
	snprintf(cpn, sizeof(cpn), "%s/%s", a->CATEGORY, a->PN);
	*q = add_set_unique(cpn, *q, NULL);
	return 0;
}

/* DDD: note, this doesn't handle more complicated set files like
 *      the portage .ini files in /usr/share/portage/sets/ */
/* DDD: this code does not combine duplicate dependencies */
/* expand one known set name (leading @ removed) into q */
static set *
qmerge_expand_setname(const char *name, set *q)
{
	if (strcmp(name, "world") == 0)
		return qmerge_add_set_file(CONFIG_EPREFIX, "/var/lib/portage",
								   "world", q);
	if (strcmp(name, "all") == 0) {
		/* every installed package, via a plain VDB walk --
		 * tree_match_atom has no match-all query */
		tree_ctx *ctx = tree_new(portroot, portvdb, TREETYPE_VDB, true);

		if (ctx != NULL) {
			tree_foreach_pkg_fast(ctx, qmerge_all_cb, &q, NULL);
			tree_close(ctx);
		}
		return q;
	}
	if (strcmp(name, "system") == 0)
		return q_profile_walk("packages", qmerge_add_set_system, q);
	/* TODO: use configroot */
	return qmerge_add_set_file(CONFIG_EPREFIX,
							   "/etc/portage/sets", name, q);
}

static set *
qmerge_add_set(char *buf, set *q)
{
	char *name = NULL;
	char *at;

	rmspace(buf);

	/* leading @ = a set reference (@world, @system, @myset); the bare
	 * words world/system/all stay as historic aliases */
	if (buf[0] == '@')
		name = buf + 1;
	else if (strcmp(buf, "world") == 0 || strcmp(buf, "all") == 0 ||
			 strcmp(buf, "system") == 0)
		name = buf;

	if (name != NULL) {
		/* @set@binrepo: expand the set, pinning EVERY member to that
		 * binhost; plain @set resolves priority-first as usual */
		char *pin = strchr(name, '@');

		if (pin != NULL && pin[1] != '\0') {
			set    *tmp;
			array  *keys;
			size_t  i;
			char   *k;

			*pin++ = '\0';
			tmp  = qmerge_expand_setname(name, NULL);
			keys = tmp != NULL ? set_keys(tmp) : NULL;
			if (keys != NULL) {
				array_for_each(keys, i, k) {
					char pinned[_Q_PATH_MAX];

					snprintf(pinned, sizeof(pinned), "%s::@%s", k, pin);
					q = add_set_unique(pinned, q, NULL);
				}
				array_free(keys);
			}
			if (tmp != NULL)
				free_set(tmp);
			return q;
		}
		return qmerge_expand_setname(name, q);
	}

	/* pkg@binrepo: explicit binhost selector (distinct sigil, so
	 * ::repo keeps its classic ebuild-repo meaning); rewritten to
	 * the internal ::@name marker the resolver keys on. */
	at = strchr(buf + 1, '@');
	if (at != NULL && at[1] != '\0') {
		char tmp[_Q_PATH_MAX];

		*at = '\0';
		snprintf(tmp, sizeof(tmp), "%s::@%s", buf, at + 1);
		return add_set_unique(tmp, q, NULL);
	}
	return add_set_unique(buf, q, NULL);
}

/* -s: regex search over the binhost Packages catalog.  Read-only, index
 * only, never opens a .gpkg, so it works on a fresh box that has only
 * fetched the index via qmerge -f and not downloaded any package yet.  The
 * remote index carries no DESCRIPTION/HOMEPAGE, so matching is by name
 * (cat/pn), the one axis a binhost consumer can rely on. */
struct qm_search_state {
	regex_t *res;
	int      npat;
	set     *cpns;
};

static int
qm_search_cb(tree_pkg_ctx *pkg, void *priv)
{
	struct qm_search_state *st   = priv;
	depend_atom            *atom = tree_pkg_atom(pkg, true);
	char                    cpn[_Q_PATH_MAX];
	int                     i;
	bool                    match;

	if (atom == NULL || atom->CATEGORY == NULL || atom->PN == NULL)
		return 0;

	/* plain string, NOT atom_format: that embeds ANSI color codes when
	 * stdout is a tty, which breaks both regexec and the set keys */
	snprintf(cpn, sizeof(cpn), "%s/%s", atom->CATEGORY, atom->PN);

	if (st->npat == 0) {
		match = true;   /* no pattern: list the whole catalog */
	} else {
		match = false;
		for (i = 0; i < st->npat; i++) {
			if (regexec(&st->res[i], cpn, 0, NULL, 0) == 0 ||
					regexec(&st->res[i], atom->PN, 0, NULL, 0) == 0) {
				match = true;
				break;
			}
		}
	}

	if (match)
		st->cpns = add_set_unique(cpn, st->cpns, NULL);

	return 0;
}

/* emerge -va style USE/USE_EXPAND rendering for a binpkg candidate,
 * coloured and markered against the installed copy (output_helpers
 * _create_use_string semantics: red/blue unchanged, green* toggled,
 * yellow% new-in-IUSE; ipkg NULL = fresh install, plain red/blue).
 * USE_EXPAND groups (PYTHON_TARGETS etc.) render as NAME="..." with
 * the prefix stripped, in the profile's USE_EXPAND order. */
static void
qm_use_string(tree_pkg_ctx *bv, tree_pkg_ctx *iv, char *out, size_t osz)
{
	char   *iusestr = tree_pkg_meta(bv, Q_IUSE);
	set    *bu;
	set    *iu      = NULL;
	set    *oldiuse = NULL;
	char  **exp     = NULL;
	size_t  nexp    = 0;
	char   *expdup  = NULL;
	size_t  olen    = 0;
	size_t  gi;

	out[0] = '\0';
	if (iusestr == NULL || *iusestr == '\0')
		return;

	bu = qm_flags_to_set(tree_pkg_meta(bv, Q_USE));
	if (iv != NULL) {
		iu      = qm_flags_to_set(tree_pkg_meta(iv, Q_USE));
		oldiuse = qm_flags_to_set(tree_pkg_meta(iv, Q_IUSE));
	}

	/* USE_EXPAND group names from the profile/config */
	if (use_expand != NULL && *use_expand != '\0') {
		char *tok;
		char *sp;

		expdup = xstrdup(use_expand);
		for (tok = strtok_r(expdup, " \t", &sp);
			 tok != NULL;
			 tok = strtok_r(NULL, " \t", &sp)) {
			exp = xrealloc(exp, sizeof(*exp) * (nexp + 1));
			exp[nexp++] = tok;
		}
	}

	/* group 0 = plain USE, groups 1..nexp = USE_EXPAND in order */
	for (gi = 0; gi <= nexp; gi++) {
		char   pfx[128] = "";
		size_t pfxlen   = 0;
		bool   opened   = false;
		int    pass;

		if (gi > 0) {
			size_t x;

			snprintf(pfx, sizeof(pfx), "%s_", exp[gi - 1]);
			for (x = 0; pfx[x] != '\0'; x++)
				pfx[x] = (char)tolower((unsigned char)pfx[x]);
			pfxlen = strlen(pfx);
		}

		/* enabled flags first, then disabled, emerge ordering */
		for (pass = 0; pass < 2; pass++) {
			char *tmp = xstrdup(iusestr);
			char *tok;
			char *sp;

			for (tok = strtok_r(tmp, " \t\n", &sp);
				 tok != NULL;
				 tok = strtok_r(NULL, " \t\n", &sp)) {
				const char *show;
				const char *col;
				const char *mark;
				bool        enabled;
				bool        known;
				bool        was_on;
				size_t      xi;
				bool        in_other = false;

				if (*tok == '+' || *tok == '-')
					tok++;
				if (*tok == '\0')
					continue;

				/* does this flag belong to the current group? */
				if (gi > 0) {
					if (strncmp(tok, pfx, pfxlen) != 0)
						continue;
				} else {
					for (xi = 0; xi < nexp; xi++) {
						char p2[128];
						size_t x;

						snprintf(p2, sizeof(p2), "%s_", exp[xi]);
						for (x = 0; p2[x] != '\0'; x++)
							p2[x] = (char)tolower((unsigned char)p2[x]);
						if (strncmp(tok, p2, strlen(p2)) == 0) {
							in_other = true;
							break;
						}
					}
					if (in_other)
						continue;
				}

				enabled = contains_set(tok, bu) != NULL;
				if ((pass == 0) != enabled)
					continue;
				known  = iv == NULL ||
						 contains_set(tok, oldiuse) != NULL;
				was_on = iv != NULL && iu != NULL &&
						 contains_set(tok, iu) != NULL;

				if (iv == NULL) {
					col  = enabled ? "\033[31;01m" : "\033[34;01m";
					mark = "";
				} else if (enabled) {
					if (!known)      { col = "\033[33;01m"; mark = "%*"; }
					else if (was_on) { col = "\033[31;01m"; mark = "";   }
					else             { col = "\033[32;01m"; mark = "*";  }
				} else {
					if (!known)      { col = "\033[33;01m"; mark = "%";  }
					else if (was_on) { col = "\033[32;01m"; mark = "*";  }
					else             { col = "\033[34;01m"; mark = "";   }
				}
				if (*NORM == '\0')
					col = "";

				show = gi > 0 ? tok + pfxlen : tok;
				if (olen + strlen(show) + strlen(pfx) + 32 >= osz)
					break;
				if (!opened) {
					char gname[128];

					if (gi > 0)
						snprintf(gname, sizeof(gname), "%s", exp[gi - 1]);
					olen += (size_t)snprintf(out + olen, osz - olen,
							"%s%.100s=\"", olen > 0 ? " " : "  ",
							gi > 0 ? gname : "USE");
					opened = true;
				}
				olen += (size_t)snprintf(out + olen, osz - olen,
						"%s%s%s%s%s%s",
						out[olen - 1] == '"' ? "" : " ",
						col, enabled ? "" : "-", show, NORM, mark);
			}
			free(tmp);
		}
		if (opened && olen + 2 < osz)
			olen += (size_t)snprintf(out + olen, osz - olen, "\"");
	}

	free(expdup);
	free(exp);
	free_set(bu);
	if (iu != NULL)
		free_set(iu);
	if (oldiuse != NULL)
		free_set(oldiuse);
}

/* one emerge -pvK style search result line for candidate bv (installed
 * comparison against iv); note, when set, is appended as annotation */
static void
qm_search_print_line(const char *cpn, tree_pkg_ctx *bv, tree_pkg_ctx *iv,
					 const char *note)
{
	depend_atom *ba   = tree_pkg_atom(bv, true);
	char        *bid  = tree_pkg_meta(bv, Q_BUILD_ID);
	char        *repo = tree_pkg_meta(bv, Q_repository);
	char        *sz   = tree_pkg_meta(bv, Q_SIZE);
	const char  *stf;
	const char  *color;
	char         oldv[128] = "";

	if (iv == NULL) {
		stf   = " N     ";
		color = GREEN;
	} else {
		depend_atom *ia = tree_pkg_atom(iv, true);

		switch (atom_compare(ba, ia)) {
		case EQUAL:
			stf   = "  R    ";
			color = YELLOW;
			break;
		case NEWER:
			stf   = "    U  ";
			color = BLUE;
			break;
		case OLDER:
			stf   = "    UD ";
			color = DKBLUE;
			break;
		default:
			stf   = "  ?    ";
			color = RED;
			break;
		}
		if (stf[4] == 'U') {
			snprintf(oldv, sizeof(oldv), " %s[%s", DKBLUE, ia->PVR);
			if (ia->SLOT != NULL) {
				size_t ol = strlen(oldv);
				snprintf(oldv + ol, sizeof(oldv) - ol, ":%s", ia->SLOT);
			}
			{
				size_t ol = strlen(oldv);
				snprintf(oldv + ol, sizeof(oldv) - ol, "]%s", NORM);
			}
		}
	}

	printf("[%sbinary%s %s%s%s] %s%s%s-%s",
		   MAGENTA, NORM, color, stf, NORM,
		   MAGENTA, cpn, NORM, ba->PVR);
	if (bid != NULL && *bid != '\0')
		printf("-%s", bid);
	if (ba->SLOT != NULL) {
		printf("%s:%s", CYAN, ba->SLOT);
		if (ba->SUBSLOT != NULL && strcmp(ba->SLOT, ba->SUBSLOT) != 0)
			printf("/%s", ba->SUBSLOT);
		printf("%s", NORM);
	}
	if (repo != NULL && *repo != '\0')
		printf("%s::%s%s", DKBLUE, repo, NORM);
	printf("%s", oldv);
	if (verbose) {
		char usebuf[4096];

		qm_use_string(bv, iv, usebuf, sizeof(usebuf));
		if (usebuf[0] != '\0')
			printf("%s", usebuf);
	}
	if (sz != NULL && *sz != '\0')
		printf("  %llu KiB",
			   (unsigned long long)(strtoull(sz, NULL, 10) / 1024));
	/* binhost provenance: which configured binrepo serves this pkg
	 * (only meaningful with more than one) */
	if (qm_nbinrepos > 1) {
		const char *rn = qm_repo_name_of_pkg(bv);

		if (rn != NULL)
			printf("  %s[%s]%s", qm_repo_tag_color(), rn, NORM);
	}
	if (note != NULL)
		printf("  %s", note);
	printf("\n");
}

/* read one archive member fully into memory; NULL when absent */
static char *
qm_arch_slurp(struct archive *a, size_t *lenp)
{
	char   *buf = NULL;
	size_t  cap = 0;
	size_t  len = 0;
	ssize_t r;

	for (;;) {
		if (len + BUFSIZ > cap) {
			cap = cap == 0 ? 65536 : cap * 2;
			buf = xrealloc(buf, cap);
		}
		r = archive_read_data(a, buf + len, cap - len);
		if (r < 0) {
			free(buf);
			return NULL;
		}
		if (r == 0)
			break;
		len += (size_t)r;
	}
	*lenp = len;
	return buf;
}

/* extract the serialized build environment (metadata/environment.bz2)
 * from a gpkg, decompressed, as a NUL-terminated string */
static char *
qm_gpkg_environment(const char *gpkg_path)
{
	struct archive       *a;
	struct archive_entry *e;
	char                 *mdbuf  = NULL;
	size_t                mdlen  = 0;
	char                 *envbz  = NULL;
	size_t                envlen = 0;
	char                 *txt    = NULL;
	size_t                txtlen = 0;

	/* outer container: find metadata.tar.* (not its .sig) */
	a = archive_read_new();
	archive_read_support_format_all(a);
	if (archive_read_open_filename(a, gpkg_path, BUFSIZ) != ARCHIVE_OK) {
		archive_read_free(a);
		return NULL;
	}
	while (archive_read_next_header(a, &e) == ARCHIVE_OK) {
		const char *fn = archive_entry_pathname(e);
		const char *b  = strrchr(fn, '/');
		size_t      bl;

		b  = b != NULL ? b + 1 : fn;
		bl = strlen(b);
		if (strncmp(b, "metadata.tar", sizeof("metadata.tar") - 1) == 0 &&
				!(bl > 4 && strcmp(b + bl - 4, ".sig") == 0)) {
			mdbuf = qm_arch_slurp(a, &mdlen);
			break;
		}
	}
	archive_read_free(a);
	if (mdbuf == NULL)
		return NULL;

	/* inner metadata tar (any compression): environment.bz2 */
	a = archive_read_new();
	archive_read_support_format_all(a);
	archive_read_support_filter_all(a);
	if (archive_read_open_memory(a, mdbuf, mdlen) != ARCHIVE_OK) {
		archive_read_free(a);
		free(mdbuf);
		return NULL;
	}
	while (archive_read_next_header(a, &e) == ARCHIVE_OK) {
		const char *fn = archive_entry_pathname(e);
		const char *b  = strrchr(fn, '/');

		b = b != NULL ? b + 1 : fn;
		if (strcmp(b, "environment.bz2") == 0) {
			envbz = qm_arch_slurp(a, &envlen);
			break;
		}
	}
	archive_read_free(a);
	free(mdbuf);
	if (envbz == NULL)
		return NULL;

	/* the bz2 blob itself */
	a = archive_read_new();
	archive_read_support_format_raw(a);
	archive_read_support_filter_all(a);
	if (archive_read_open_memory(a, envbz, envlen) != ARCHIVE_OK) {
		archive_read_free(a);
		free(envbz);
		return NULL;
	}
	if (archive_read_next_header(a, &e) == ARCHIVE_OK)
		txt = qm_arch_slurp(a, &txtlen);
	archive_read_free(a);
	free(envbz);
	if (txt == NULL)
		return NULL;

	txt = xrealloc(txt, txtlen + 1);
	txt[txtlen] = '\0';
	return txt;
}

/* print one named function definition from the environment; while
 * printing, collect callee names containing "_pkg_" (eclass phase
 * helpers like toolchain_pkg_postinst) into `callees` when given */
static bool
qm_env_print_func(const char *env, const char *name, set **callees)
{
	const char *p     = env;
	size_t      nlen  = strlen(name);
	bool        in_f  = false;
	bool        found = false;

	while (p != NULL && *p != '\0') {
		const char *nl   = strchr(p, '\n');
		size_t      llen = nl != NULL ? (size_t)(nl - p) : strlen(p);

		if (!in_f) {
			if (llen >= nlen + 4 &&
					strncmp(p, name, nlen) == 0 &&
					strncmp(p + nlen, " () ", 4) == 0) {
				in_f  = true;
				found = true;
				printf("%s%.*s%s\n", GREEN, (int)llen, p, NORM);
			}
		} else {
			printf("%.*s\n", (int)llen, p);
			if (callees != NULL) {
				const char *m = p;
				const char *e = p + llen;

				while ((m = memmem(m, (size_t)(e - m),
								   "_pkg_", 5)) != NULL) {
					const char *b = m;
					const char *f = m + 5;
					char        fname[128];

					while (b > p && (isalnum((unsigned char)b[-1]) ||
									 b[-1] == '_' || b[-1] == '-'))
						b--;
					while (f < e && (isalnum((unsigned char)*f) ||
									 *f == '_'))
						f++;
					if (b < m && (size_t)(f - b) < sizeof(fname)) {
						snprintf(fname, sizeof(fname), "%.*s",
								 (int)(f - b), b);
						*callees = add_set_unique(fname, *callees, NULL);
					}
					m = f;
				}
			}
			if (llen == 1 && p[0] == '}') {
				in_f = false;
				if (nl == NULL)
					break;
			}
		}
		if (nl == NULL)
			break;
		p = nl + 1;
	}
	return found;
}

/* print every pkg_* function definition found in the environment, then
 * one level of the eclass helpers they delegate to */
static int
qm_env_print_pkg_funcs(const char *env)
{
	static const char *want[] = {
		"pkg_pretend", "pkg_setup", "pkg_preinst", "pkg_postinst",
		"pkg_prerm", "pkg_postrm", "pkg_config", "pkg_info",
		"pkg_nofetch"
	};
	set    *callees = NULL;
	size_t  wi;
	int     cnt = 0;

	for (wi = 0; wi < ARRAY_SIZE(want); wi++)
		if (qm_env_print_func(env, want[wi], &callees))
			cnt++;

	if (callees != NULL) {
		array  *keys = set_keys(callees);
		size_t  n;
		char   *cn;

		array_for_each(keys, n, cn) {
			bool skip = false;

			for (wi = 0; wi < ARRAY_SIZE(want); wi++)
				if (strcmp(cn, want[wi]) == 0)
					skip = true;
			if (skip)
				continue;
			printf("%s# delegated:%s\n", DKBLUE, NORM);
			(void)qm_env_print_func(env, cn, NULL);
		}
		array_free(keys);
		free_set(callees);
	}
	return cnt;
}

/* --show-phases: resolve each atom (pkg@repo works), fetch the gpkg if
 * needed, and print the pkg_* hook bodies frozen inside it, read the
 * code before answering Y */
static int
qm_show_phases(int nargs, char **args)
{
	int ret = EXIT_SUCCESS;
	int i;

	for (i = 0; i < nargs; i++) {
		char          abuf[_Q_PATH_MAX];
		char         *at;
		atom_ctx     *a;
		tree_pkg_ctx *bpkg;
		char          path[_Q_PATH_MAX];
		char         *env;
		const char   *rn;
		char         *dp;

		/* pkg@binrepo sigil, same rewrite as the install path */
		snprintf(abuf, sizeof(abuf), "%s", args[i]);
		at = strchr(abuf + 1, '@');
		if (at != NULL && at[1] != '\0') {
			char tmp[_Q_PATH_MAX + 8];

			*at = '\0';
			if ((size_t)snprintf(tmp, sizeof(tmp), "%s::@%s",
								 abuf, at + 1) < sizeof(abuf))
				snprintf(abuf, sizeof(abuf), "%.*s",
						 (int)(sizeof(abuf) - 1), tmp);
		}

		a = atom_explode(abuf);
		if (a == NULL) {
			warn("invalid atom: %s", args[i]);
			ret = EXIT_FAILURE;
			continue;
		}
		bpkg = best_version(a, BV_BINPKG);
		if (bpkg == NULL) {
			warn("cannot satisfy %s from any binhost", args[i]);
			atom_implode(a);
			ret = EXIT_FAILURE;
			continue;
		}
		if (!pkg_download(bpkg)) {
			atom_implode(a);
			ret = EXIT_FAILURE;
			continue;
		}

		snprintf(path, sizeof(path), "%s%s", portroot,
				 tree_pkg_get_path(bpkg));
		rn = qm_repo_name_of_pkg(bpkg);
		dp = tree_pkg_meta(bpkg, Q_DEFINED_PHASES);

		printf("%s===%s %s%s%s%s%s%s  DEFINED_PHASES: %s\n",
			   BOLD, NORM, MAGENTA,
			   atom_format("%[CAT]%[PF]", tree_pkg_atom(bpkg, true)),
			   NORM,
			   rn != NULL ? "  [" : "", rn != NULL ? rn : "",
			   rn != NULL ? "]" : "",
			   dp != NULL && *dp != '\0' ? dp : "(none)");

		env = qm_gpkg_environment(path);
		if (env == NULL) {
			warn("cannot extract environment from %s", path);
			atom_implode(a);
			ret = EXIT_FAILURE;
			continue;
		}
		if (qm_env_print_pkg_funcs(env) == 0)
			printf("(no pkg_* functions defined)\n");
		printf("\n");
		free(env);
		atom_implode(a);
	}
	return ret;
}

static int
qm_search_binpkgs(int npat, char **pats)
{
	struct qm_search_state  st;
	regex_t                *res = NULL;
	array                  *keys;
	size_t                  n;
	size_t                  ri;
	size_t                  rcnt = qm_bintree_cnt();
	bool                    anytree = false;
	char                   *cpn;
	int                     i;
	int                     found = 0;

	for (ri = 0; ri < rcnt; ri++)
		if (qm_bintree(ri) != NULL)
			anytree = true;
	if (!anytree) {
		warn("no binary package index found; run `qmerge -f' first");
		return EXIT_FAILURE;
	}

	if (npat > 0) {
		res = xmalloc(sizeof(*res) * npat);
		for (i = 0; i < npat; i++) {
			int r = regcomp(&res[i], pats[i],
							REG_EXTENDED | REG_ICASE | REG_NOSUB);
			if (r != 0) {
				char eb[256];
				regerror(r, &res[i], eb, sizeof(eb));
				warn("invalid search pattern `%s': %s", pats[i], eb);
				while (i-- > 0)
					regfree(&res[i]);
				free(res);
				return EXIT_FAILURE;
			}
		}
	}

	st.res  = res;
	st.npat = npat;
	st.cpns = NULL;

	/* collect names across every repo's catalog (trees sharing a store
	 * were deduped to the same pointer; skip repeats) */
	for (ri = 0; ri < rcnt; ri++) {
		tree_ctx *bt = qm_bintree(ri);
		size_t    rj;
		bool      seen = false;

		if (bt == NULL)
			continue;
		for (rj = 0; rj < ri; rj++)
			if (qm_bintrees[rj] == bt)
				seen = true;
		if (seen)
			continue;
		tree_foreach_pkg_sorted(bt, qm_search_cb, &st, NULL);
	}

	keys = st.cpns != NULL ? set_keys(st.cpns) : NULL;
	if (keys != NULL) {
		array_for_each(keys, n, cpn) {
			depend_atom  *a = atom_explode(cpn);
			tree_pkg_ctx *bv;
			tree_pkg_ctx *iv;

			if (a == NULL)
				continue;

			/* best_version applies the same mask/keyword/license gates
			 * the resolver uses, so results == what qmerge could merge;
			 * -v also lists names with no currently installable binpkg */
			bv = best_version(a, BV_BINPKG);
			if (bv == NULL && !verbose) {
				atom_implode(a);
				continue;
			}
			iv = best_version(a, BV_VDB);

			/* emerge -pvK line format:
			 * [binary   R    ] cat/pn-PVR-BID:SLOT/SUB::repo [old] SIZE KiB */
			if (bv == NULL) {
				/* only reached with -v */
				printf("[%sbinary%s        ] %s%s%s (no installable binpkg)\n",
					   GREEN, NORM, BOLD, cpn, NORM);
			} else {
				qm_search_print_line(cpn, bv, iv, NULL);

				/* -v with several binrepos: also list what the OTHER
				 * repos carry for this name, annotated with why it was
				 * not selected */
				if (verbose && qm_nbinrepos > 1) {
					ssize_t w     = qm_repoidx_of_pkg(bv);
					size_t  vrcnt = qm_bintree_cnt();
					size_t  vri;

					for (vri = 0; vri < vrcnt; vri++) {
						tree_ctx     *bt;
						array        *t;
						size_t        cn;
						tree_pkg_ctx *cand;
						tree_pkg_ctx *rbest  = NULL;
						bool          usebad = false;

						if ((ssize_t)vri == w)
							continue;
						bt = qm_bintree(vri);
						if (bt == NULL ||
								(w >= 0 && qm_bintrees[w] == bt))
							continue;

						t = tree_match_atom(bt, a,
								TREE_MATCH_SORT | TREE_MATCH_VIRTUAL |
								TREE_MATCH_ACCT);
						array_for_each(t, cn, cand) {
							depend_atom *pa = tree_pkg_atom(cand, true);

							if (binpkg_masked(pa) ||
									!binpkg_keywords_ok(cand, pa, true) ||
									!binpkg_license_ok(cand, pa, true) ||
									binpkg_excluded(cand, pa, true))
								continue;
							rbest  = cand;
							{
								char why[128];

								usebad = qm_respect_use != 0 &&
										(vri > 0 || qm_respect_use == 1) &&
										!binpkg_use_ok_r(cand, pa,
												qm_nbinrepos > 0 ?
												qm_binrepos[vri].name : NULL,
												why, sizeof(why));
							}
							break;
						}
						array_free(t);

						if (rbest == NULL)
							continue;
						qm_search_print_line(cpn, rbest, iv,
								usebad ? "(USE mismatch)" :
								(ssize_t)vri > w ?
								"(not selected: lower priority)" :
								"(not selected)");
					}
				}
			}
			found++;
			atom_implode(a);
		}
		array_free(keys);
	}

	if (res != NULL) {
		for (i = 0; i < npat; i++)
			regfree(&res[i]);
		free(res);
	}
	if (st.cpns != NULL)
		free_set(st.cpns);

	if (found == 0)
		warn("no matching packages in the binhost index");

	return found > 0 ? EXIT_SUCCESS : EXIT_FAILURE;
}

static int
qmerge_run(set *todo)
{
	if (uninstall) {
		return unmerge_packages(todo);
	} else {
		if (todo == NULL) {
			/* -s is dispatched earlier in qmerge_main */
			warn("nothing to do");

			return EXIT_SUCCESS;
		} else {
			/* full transitive resolution (emerge-style), then merge
			 * the resulting plan in dependency order */
			return qm_resolve_and_merge(todo);
		}
	}
}

/* portage --jobs grammar: n=serial, y/True=unlimited (capped), 0=one per
 * CPU, N=that many.  Shared by the -j flag and $QMERGE_JOBS. */
static int
qm_parse_jobs(const char *s)
{
	int j;

	if (strcmp(s, "n") == 0)
		return 1;
	if (strcmp(s, "y") == 0 || strcmp(s, "True") == 0)
		return 16;
	j = atoi(s);
	if (j == 0)
		j = (int)sysconf(_SC_NPROCESSORS_ONLN);
	return j < 1 ? 1 : j;
}

int qmerge_main(int argc, char **argv)
{
	int i, ret;
	set *todo;
	bool regen_index = false;

	if (getenv("QMERGE_SELFTEST") != NULL)
		return qm_resolver_selftest();

	if (argc < 2)
		qmerge_usage(EXIT_FAILURE);

	/* QMERGE_NOCOLOR from make.conf/env: qmerge-only colorless output;
	 * applied before getopt so an explicit --color still wins */
	if (qmerge_nocolor && !nocolor) {
		nocolor = true;
		color_clear();
		setenv("NOCOLOR", "true", 1);
	}

	while ((i = GETOPT_LONG(QMERGE, qmerge, "")) != -1) {
		switch (i) {
			case 'f': force_download = 1;  break;
			case 'F': force_download = 2;  break;
			case 's': search_pkgs = 1;
					  interactive = 0;     break;
			case 131: show_phases = 1;
					  interactive = 0;     break;
			case 132: qm_backtrack = atoi(optarg); break;
			/* case 'i': case 'g': */
			case 'K': install = 1;         break;
			case 'U': uninstall = 1;       break;
			case 'e': uninstall = 1;
					  uninstall_force = 1; break;
			case 'p': pretend = 1;         break;
			case 'N': newuse = 1;          break;
			case 133: rebuilt_bins = 1;    break;
			case 137: qm_rebuilt_ts = strtoull(optarg, NULL, 10); break;
			case 'u': update_only = 1;
					  install = 1;         break;
			case 'D': deep = 1;
					  install = 1;         break;
			case 'y': interactive = 0;     break;
			case 'O': follow_rdepends = 0; break;
			case 'i': regen_index = true;   break;
			case 130: fetch_only = 1;
					  force_download = 1;   break;
			case 'j': qmerge_jobs = qm_parse_jobs(optarg); break;
			case 134: qm_parse_usepkg_exclude(optarg, "--usepkg-exclude");
					  break;
			case 135: qm_excl_live = 1;    break;
			case 136: qm_respect_use = (*optarg == 'y' || *optarg == '1' ||
										*optarg == 't' || *optarg == 'T')
										? 1 : 0;
					  break;
			case 127: keep_work = true;    break;
			case 128: debug = true;        break;
			COMMON_GETOPTS_CASES(qmerge)
		}
	}

	if (regen_index)
		return binpkg_index_regen();

	/* -q (quiet) only reduces output; it must NOT imply the merge prompt is
	 * skipped, use -y for non-interactive/auto-confirm.  For fully
	 * unattended runs combine them: `qmerge -f -q -y <pkg>`. */

	/* backtrack precedence: --backtrack beats $QMERGE_BACKTRACK beats
	 * the built-in default (portage's is 20) */
	if (qm_backtrack < 0) {
		const char *eb = getenv("QMERGE_BACKTRACK");

		qm_backtrack = eb != NULL && *eb != '\0' ? atoi(eb) : 20;
	}

	/* jobs precedence: -j (already set qmerge_jobs >= 0) beats
	 * QMERGE_JOBS (env beats make.conf, per the config framework)
	 * beats the built-in default */
	if (qmerge_jobs < 0) {
		qmerge_jobs = qmerge_jobs_conf != NULL && *qmerge_jobs_conf != '\0'
				? qm_parse_jobs(qmerge_jobs_conf) : 4;
	}

	/* exclusion precedence: --usepkg-exclude beats $QMERGE_USEPKG_EXCLUDE */
	if (qm_usepkg_excl == NULL) {
		const char *ee = getenv("QMERGE_USEPKG_EXCLUDE");

		if (ee != NULL && *ee != '\0')
			qm_parse_usepkg_exclude(ee, "QMERGE_USEPKG_EXCLUDE");
	}
	if (!qm_excl_live) {
		const char *el = getenv("QMERGE_USEPKG_EXCLUDE_LIVE");

		if (el != NULL && *el != '\0' && strcmp(el, "0") != 0)
			qm_excl_live = 1;
	}

	/* --binpkg-respect-use beats $QMERGE_BINPKG_RESPECT_USE */
	if (qm_respect_use < 0) {
		const char *ru = getenv("QMERGE_BINPKG_RESPECT_USE");

		if (ru != NULL && *ru != '\0')
			qm_respect_use = (*ru == 'y' || *ru == '1' ||
							  *ru == 't' || *ru == 'T') ? 1 : 0;
	}

	/* default to install if no action given */
	if (!install && !uninstall)
		install = 1;

	if (uninstall_force)
		warn("-e/--erase: shared-file protection is OFF; files co-owned by "
			 "other installed packages will be removed too (CONFIG_PROTECT "
			 "is still honored)");

	qmerge_strict = contains_set("strict", features) ? 1 : 0;

	/* Expand any portage sets on the command line (not for -s or
	 * --show-phases: their arguments are handled raw) */
	todo = NULL;
	if (!search_pkgs && !show_phases)
		for (i = optind; i < argc; ++i)
			todo = qmerge_add_set(argv[i], todo);

	if (search_pkgs == 0 && show_phases == 0 && todo == NULL &&
			force_download != 1) {
		warn("need package names to work with");
		return EXIT_FAILURE;
	}

	/* -s with no local Packages index: bootstrap by fetching it, so a
	 * fresh binhost consumer can search right away; -fs forces a
	 * refresh even when a cached index exists.  Check every repo's
	 * OWN store (location= aware), checking PKGDIR alone forced a
	 * refetch on every search when the sole repo stores elsewhere. */
	if (search_pkgs && force_download == 0) {
		size_t ri;
		size_t rcnt  = qm_bintree_cnt();
		bool   found = false;

		for (ri = 0; ri < rcnt; ri++) {
			char        locbuf[_Q_PATH_MAX];
			const char *loc = qm_nbinrepos > 0 ?
					qm_repo_loc(ri, locbuf, sizeof(locbuf)) : pkgdir;
			char        idx[_Q_PATH_MAX];
			struct stat st;

			if ((size_t)snprintf(idx, sizeof(idx), "%s%s/%s",
								 portroot, loc, Packages) >= sizeof(idx))
				continue;
			if (stat(idx, &st) == 0 && st.st_size > 0) {
				found = true;
				break;
			}
		}
		if (!found)
			force_download = 1;
	}

	if (!uninstall)
		qmerge_initialize();

	if (search_pkgs) {
		ret = qm_search_binpkgs(argc - optind, argv + optind);
		goto cleanup;
	}

	if (show_phases) {
		if (argc - optind < 1) {
			warn("--show-phases needs package names");
			ret = EXIT_FAILURE;
		} else {
			ret = qm_show_phases(argc - optind, argv + optind);
		}
		goto cleanup;
	}

	/* -f with no packages: the index refresh done by
	 * qmerge_initialize above is the whole job (catalog sync) */
	if (todo == NULL && force_download == 1) {
		ret = EXIT_SUCCESS;
		goto cleanup;
	}

	/* merge history: record this invocation like portage does (only
	 * install/unmerge flows reach here; search and -f-only do not) */
	{
		char    cl[1024];
		size_t  off = 0;
		int     ai;
		char    db[64];
		time_t  now = time(NULL);

		strftime(db, sizeof(db), "%b %d, %Y %H:%M:%S", localtime(&now));
		qm_elog("Started emerge on: %s", db);
		for (ai = 1; ai < argc && off < sizeof(cl) - 2; ai++)
			off += (size_t)snprintf(cl + off, sizeof(cl) - off, " %s",
									argv[ai]);
		qm_elog(" *** emerge (qmerge)%s", cl);
	}

	/* Make sure the user wants to do it */
	if (interactive) {
		int save_pretend = pretend;
		int save_verbose = verbose;
		int save_quiet = quiet;

		/* start the dry run with a clean queued-packages state */
		if (_qmerge_processed_pkgs != NULL) {
			free_set(_qmerge_processed_pkgs);
			_qmerge_processed_pkgs = NULL;
		}

		pretend = save_pretend ? 10 : 100;
		verbose = 0;
		quiet = 1;
		ret = qmerge_run(todo);
		if (ret != EXIT_SUCCESS || save_pretend)
			goto cleanup;

		if (uninstall) {
			if (!qmerge_prompt("OK to unmerge these packages")) {
				ret = EXIT_FAILURE;
				goto cleanup;
			}
		} else {
			if (!qmerge_prompt("OK to merge these packages")) {
				ret = EXIT_FAILURE;
				goto cleanup;
			}
		}

		/* reset queued-packages state for the real run */
		if (_qmerge_processed_pkgs != NULL) {
			free_set(_qmerge_processed_pkgs);
			_qmerge_processed_pkgs = NULL;
		}

		pretend = save_pretend;
		verbose = save_verbose;
		quiet = save_quiet;
	}

	qm_run_trust_helper();

	ret = qmerge_run(todo);

 cleanup:
	if (todo != NULL)
		free_set(todo);

	if (_qmerge_processed_pkgs != NULL) {
		free_set(_qmerge_processed_pkgs);
		_qmerge_processed_pkgs = NULL;
	}

	while (qm_nbinrepos > 0) {
		qm_nbinrepos--;
		free(qm_binrepos[qm_nbinrepos].name);
		free(qm_binrepos[qm_nbinrepos].uri);
		free(qm_binrepos[qm_nbinrepos].loc);
	}
	free(qm_binrepos);
	qm_binrepos = NULL;

	if (qm_bintrees != NULL) {
		size_t ti;
		size_t tj;

		for (ti = 0; ti < qm_nbintrees; ti++) {
			bool shared = false;

			if (qm_bintrees[ti] == NULL)
				continue;
			for (tj = 0; tj < ti; tj++)
				if (qm_bintrees[tj] == qm_bintrees[ti])
					shared = true;
			if (!shared)
				tree_close(qm_bintrees[ti]);
		}
		free(qm_bintrees);
		qm_bintrees  = NULL;
		qm_nbintrees = 0;
	}
	/* close the merge history for logged (install/unmerge) runs */
	if (qm_elogf != NULL) {
		if (ret == EXIT_SUCCESS)
			qm_elog(" *** exiting successfully.");
		else
			qm_elog(" *** exiting unsuccessfully with status '%d'.", ret);
		qm_elog(" *** terminating.");
		fclose(qm_elogf);
		qm_elogf = NULL;
	}

	if (qm_use_rejects != NULL) {
		free_set(qm_use_rejects);
		qm_use_rejects = NULL;
	}
	if (qm_lic_rejects != NULL) {
		free_set(qm_lic_rejects);
		qm_lic_rejects = NULL;
	}
	if (qm_soft_unmerge != NULL) {
		free_set(qm_soft_unmerge);
		qm_soft_unmerge = NULL;
	}
	if (qm_usepkg_excl != NULL) {
		size_t       n;
		depend_atom *x;

		array_for_each(qm_usepkg_excl, n, x)
			atom_implode(x);
		array_free(qm_usepkg_excl);
		qm_usepkg_excl = NULL;
	}
	if (qm_plan_notices != NULL) {
		array *nv = hash_values(qm_plan_notices);

		array_deepfree(nv, (array_free_cb *)set_free);
		hash_free(qm_plan_notices);
		qm_plan_notices = NULL;
	}
	if (_qmerge_vdb_tree != NULL)
		tree_close(_qmerge_vdb_tree);

	return ret;
}
