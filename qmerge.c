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
#include <ftw.h>
#include <glob.h>
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
#include "binrepos.h"
#include "copy_file.h"
#include "dep.h"
#include "move_file.h"
#include "contents.h"
#include "eat_file.h"
#include "file_magic.h"
#include "gpkg.h"
#include "hash.h"
#include "human_readable.h"
#include "profile.h"
#include "usedep.h"
#include "rmspace.h"
#include "scandirat.h"
#include "set.h"
#include "binpath.h"
#include "moves.h"
#include "useflags.h"
#include "envd.h"
#include "tree.h"
#include "linkage.h"
#include "preserved.h"
#include "xasprintf.h"
#include "xchdir.h"
#include "xmkdir.h"
#include "xpak.h"
#include "xsystem.h"

#ifndef GLOB_BRACE
/* Expand "{a,b}" to "a" "b".  */
# define GLOB_BRACE     (1 << 10)
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
 * pkgs to be installed.
 * If for instance pkg/c depends on pkg/b it won't occur double,
 * for it is a set.
 *
 * Technically, because we deal with binpkgs, we don't have
 * dependencies, but there can be pre/post scripts that actually use
 * depended on pkgs, and if we would invoke ebuild(5) to compile instead
 * of unpack, we would respect the order too, so the resolvedset here
 * needs to be ordered into a list.
 * While functionally one can re-evaluate the dependencies here,
 * implementation wise, it probably is easier to build the final merge
 * order list while resolving.
 * This can also add the additional metadata of whether a pkg was
 * requested (cmdline) or pulled in a dep, and for which package.
 * That information can be leveraged to draw a tree (visuals) but
 * also to determine possible parallel installation paths.
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

#define QMERGE_FLAGS "fFsKUepuDNnWy1Oij:" COMMON_FLAGS
static struct option const qmerge_long_opts[] = {
	{"fetch",   no_argument, NULL, 'f'},
	{"force",   no_argument, NULL, 'F'},
	{"search",  no_argument, NULL, 's'},
	{"install", no_argument, NULL, 'K'},
	{"unmerge", no_argument, NULL, 'U'},
	{"erase",   no_argument, NULL, 'e'},
	{"deselect", opt_argument, NULL, 'W'},
	{"pretend", no_argument, NULL, 'p'},
	{"keepwork",no_argument, NULL, 127},
	{"update",  no_argument, NULL, 'u'},
	{"deep",    no_argument, NULL, 'D'},
	{"newuse",  no_argument, NULL, 'N'},
	{"noreplace", no_argument, NULL, 'n'},
	{"rebuilt-binaries", opt_argument, NULL, 133},
	{"rebuilt-binaries-timestamp", a_argument, NULL, 137},
	{"yes",     no_argument, NULL, 'y'},
	{"oneshot", no_argument, NULL, '1'},
	{"nodeps",  no_argument, NULL, 'O'},
	{"index",   no_argument, NULL, 'i'},
	{"fetchonly",no_argument, NULL, 130},
	{"show-phases",no_argument, NULL, 131},
	{"no-phases", no_argument, NULL, 143},
	{"backtrack", a_argument,  NULL, 132},
	{"jobs",    a_argument,  NULL, 'j'},
	{"usepkg-exclude", a_argument, NULL, 134},
	{"exclude", a_argument, NULL, 140},
	{"usepkg-exclude-live", no_argument, NULL, 135},
	{"binpkg-respect-use", a_argument, NULL, 136},
	{"getbinpkg-exclude", a_argument, NULL, 141},
	{"getbinpkg-include", a_argument, NULL, 142},
	{"repos",   no_argument, NULL, 138},
	{"list-set", no_argument, NULL, 144},
	{"info",    no_argument, NULL, 145},
	{"exact",   no_argument, NULL, 146},
	{"keep-going", opt_argument, NULL, 147},
	{"debug",   no_argument, NULL, 128},
	COMMON_LONG_OPTS
};
static const char * const qmerge_opts_help[] = {
	"Fetch packages (and their deps) without merging, like emerge -f; alone: refresh the Packages index",
	"Force-install the named target: newest binpkg regardless of SLOT, ignoring mask/keyword/license/respect-use/usepkg-exclude (re-fetch + re-index); collision protection stays on",
	"Search the binhost catalog by name (regex, keys carrying a version, slot or operator match as atoms, name-ver = =name-ver*, -v lists non-installable, -vv every version/build instance in every repo)",
	"Install package",
	"Uninstall package",
	"Force-erase: unmerge WITHOUT the shared-file scan (only CONFIG_PROTECT kept)",
	"Remove atoms/@sets from the world file (implied by -U/-e; =n prevents that)",
	"Pretend only",
	"Do not cleanup the unpacked binpkgs in qmerge tempdir",
	"Update only",
	"Consider the whole dep tree for updates (deep); with -u = emerge -uD",
	"Reinstall binpkgs whose built USE (incl. *_TARGETS) differs from installed",
	"Skip named targets that are already installed (records world without merging)",
	"Reinstall same-version binpkgs the binhost rebuilt (y/n; auto-on with -D)",
	"With --rebuilt-binaries: only NEWER rebuilds with BUILD_TIME >= this epoch",
	"Don't prompt before overwriting",
	"Do not add the package(s) to the world set (emerge --oneshot)",
	"Don't merge dependencies",
	"Update the Packages index from PKGDIR (incremental; -F: full rebuild)",
	"Alias of -f",
	"Print the pkg_* phase functions a binpkg would run at merge time",
	"Bootstrap: skip pkg_* phase execution (no shell needed); skips are recorded in var/lib/portage/.qmerge-skipped-phases",
	"Conflict-repair rounds during resolution (default 20, 0 disables)",
	"Parallel download jobs: N, 0=one per CPU, y=max, n=serial (default 4)",
	"Never satisfy these atoms from binpkgs (no source fallback: refuses)",
	"Hold these atoms at their installed version and drop them from the merge without error (like emerge --exclude)",
	"Reject binpkgs built from live ebuilds (PROPERTIES=live)",
	"USE check for pkg candidates: y=full USE match on all repos, n=off (default: weak USE check, foreign repos only)",
	"Never take these atoms from any binhost (name/slot atoms only; adds to per-repo getbinpkg-exclude from binrepos.conf)",
	"Only take these atoms from binhosts (whitelist; name/slot atoms only)",
	"List the configured binhost repositories in priority order",
	"Print the expanded members of the given @set(s), one atom per line, and exit",
	"Show precisely how a package was compiled (identity, build env, dep bindings, sonames). VDB default, pkg@repo targets a binhost entry",
	"With -s: match plain keys as whole names, not substrings",
	"Continue past a failed package like emerge --keep-going: hide from the list, re-resolve, drop dependents that lost their provider, merge the rest (y/n, default n)",
	"Run shell funcs with `set -x`",
	COMMON_OPTS_HELP
};
#define qmerge_usage(ret) usage(ret, QMERGE_FLAGS, qmerge_long_opts, qmerge_opts_help, NULL, lookup_applet_idx("qmerge"))

/* all of these need to be defined.
 * for @francoisb please take care of these all.
 * I removed the others for consistency.
 * and maybe order them clearer. */
char search_pkgs = 0;
static char show_phases = 0;
static char no_phases = 0;
static const char *qm_phase_pkg = NULL;
static int qm_backtrack = -1;
char interactive = 1;
char install = 0;
char uninstall = 0;
char uninstall_force = 0;
char noreplace = 0;
static int qm_deselect = -1;
char oneshot = 0;
char force_download = 0;
char follow_rdepends = 1;
char qmerge_strict = 0;
char update_only = 0;
static char newuse = 0;
static int  rebuilt_bins = -1;
static unsigned long long qm_rebuilt_ts = 0;
static char qm_rebuilt_ts_set = 0;
static int  qm_user_quiet   = 0;
static int  qm_user_verbose = 0;
static int  qm_lenient = -1;
static int  qm_slot_unify = -1;
static set *qm_tolerated = NULL;
static bool qm_news_force = false;
char deep = 0;
char fetch_only = 0;
int  qmerge_jobs = -1;
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
static set *qmerge_processed_pkgs = NULL;
static set *qm_exec_failed = NULL;

static void
qm_exec_fail(const depend_atom *patom)
{
	char key[512];

	snprintf(key, sizeof(key), "%s/%s",
			 patom->CATEGORY != NULL ? patom->CATEGORY : "",
			 patom->PF != NULL ? patom->PF : "");
	if (qm_exec_failed == NULL)
		qm_exec_failed = create_set();
	add_set(key, qm_exec_failed);
}

/* --keep-going y|n
 *
 * we'll ideally keep exact same portage features here, so that
 * documentation will apply here as well.
 * only thing that we need to take care of is the actual C declarations
 * and implementation. I hope we get this documented faster. */
static int    qm_keep_going = -1;
static set   *qm_kg_mask    = NULL;
static hash_t *qm_kg_done   = NULL;
static array *qm_kg_failed  = NULL;
static int    qm_kg_rounds  = 0;
static int    qm_kg_fd      = -1;\
static bool   qm_kg_child   = false;

/* round pipe line. one of B(egin) O(k) S(oft-fail) P(ostinst-fail) */
static void
qm_kg_announce(char code, const char *cpv, const char *slot)
{
	if (qm_kg_fd < 0)
		return;
	dprintf(qm_kg_fd, "%c %s %s\n", code, cpv, slot != NULL ? slot : "");
}

static void
qm_kg_record(const char *cpv, const char *reason)
{
	char *e;

	if (qm_kg_failed == NULL)
		qm_kg_failed = array_new();
	xasprintf(&e, "%s\t%s", cpv, reason);
	array_append(qm_kg_failed, e);
}
static void pkg_merge(int, const depend_atom *, tree_pkg_ctx *);
static bool pkg_download(tree_pkg_ctx *);
static const char *qm_config_var(const char *name);
static void qm_env_update_hook(array *touched);
static void qm_apply_moves_all(void);
static void qm_apply_news_all(void);
static int unmerge_packages(set *);
static void qm_world_clean_unmerged(void);
static set *qm_unmerged_cps;

/* QMERGE_BLOCKERS soft-blocker auto-unmerge: installed pkgs (cat/PF) the
 * resolution soft-blocks, collected during the conflict scan, unmerged before
 * the merge.
 * NULL/empty when the feature is off or nothing to drop. */
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
 * ideally inherited from the directory. */
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

static void
binpkg_perms_fd(int fd, bool isdir)
{
	char        pdir[_Q_PATH_MAX];
	struct stat pst;
	struct stat st;
	mode_t      mask = isdir ? 02070 : 0060;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	if (stat(pdir, &pst) != 0)
		return;
	if (fchown(fd, (uid_t)-1, pst.st_gid) != 0) {
	}
	if (fstat(fd, &st) == 0)
		(void)fchmod(fd, (st.st_mode & 07777 & (mode_t)~mask) |
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
 * merge-visible when every required license is accepted.
 * Empty LICENSE accepts (nothing to accept); an unaccepted license,
 * or an @GROUP that cannot be expanded (missing license_groups), blocks.
 * ACCEPT_LICENSE is incremental; @GROUP references expand recursively;
 * package.license extends the set per atom. */
struct lic_acc {
	/* explicitly accepted licenses */
	set  *acc;
	/* explicitly denied (after a wildcard) */
	set  *den;
	/* a bare '*' was in effect */
	bool  accept_all;
	/* the binpkg's enabled USE flags */
	set  *use;
};

static void
lic_expand_group(const char *group, set *target, set *seen)
{
	const char *val;
	char       *tmp;
	char       *tok;
	char       *sp;

	if (contains_set(group, seen) != NULL)
		return;
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
		return;
	}
	tmp = xstrdup(val);
	for (tok = strtok_r(tmp, " \t", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t", &sp))
	{
		if (tok[0] == '@')
			lic_expand_group(tok + 1, target, seen);
		else if (tok[0] == '-')
			;
		else
			add_set_unique(tok, target, NULL);
	}
	free(tmp);
}

/* beautiful tokens! what are they? */
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
			if (neg) {
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
						 (int)MIN(L - 1 - (neg ? 1 : 0), sizeof(flag) - 1),
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

/* que? */
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
						 (int)MIN(L - 1 - (neg ? 1 : 0), sizeof(flag) - 1),
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
 * printed as a resolution-time block like the USE rejects */
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

	/* no ACCEPT_LICENSE at all (profile-less binhost eater, e.g. a
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

/* map the CHOST machine field to a Gentoo ARCH keyword.
 * only used when no profile provides ARCH (binhost-only eater).
 * returns NULL for an unrecognised CHOST, in which case the caller trusts the binhost. */
static const char *
qm_arch_from_chost(const char *ch)
{
	if (ch == NULL || ch[0] == '\0')
		return NULL;

	if (strncmp(ch, "x86_64", 6) == 0 || strncmp(ch, "amd64", 5) == 0)
		return "amd64";
	if (ch[0] == 'i' && ch[1] >= '3' && ch[1] <= '6' &&
		/* i386..i686 */
		strncmp(ch + 2, "86", 2) == 0)
		return "x86";
	if (strncmp(ch, "aarch64", 7) == 0)
		return "arm64";
	if (strncmp(ch, "arm", 3) == 0)
		return "arm";
	/* incl. le */
	if (strncmp(ch, "powerpc64", 9) == 0)
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
 * set, else derived from CHOST so a profile-less binhost eater still
 * gets stable-vs-~testing gating.
 * Expect NULL when neither is available. */
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

	/* global ACCEPT_KEYWORDS, incremental semantics in order: an
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

	/* matching package.accept_keywords entries extend the set: an
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
				/* -arch / -*: never acceptable */
				continue;
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

/* --getbinpkg-exclude/--getbinpkg-include  */
static array *qm_gb_excl_cli = NULL;
static array *qm_gb_incl_cli = NULL;

static void
qm_parse_gb_atoms(array **lst, const char *arg, const char *src)
{
	char *tmp = xstrdup(arg);
	char *tok;
	char *sp;

	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		depend_atom *a = atom_explode(tok);

		if (a == NULL || a->PN == NULL ||
				a->blocker != ATOM_BL_NONE ||
				a->pfx_op != ATOM_OP_NONE ||
				a->sfx_op != ATOM_OP_NONE ||
				a->PV != NULL)
		{
			warn("invalid atom in %s: %s "
				 "(only package names and slot atoms allowed)", src, tok);
			if (a != NULL)
				atom_implode(a);
			continue;
		}
		if (*lst == NULL)
			*lst = array_new();
		array_append(*lst, a);
	}
	free(tmp);
}

static ssize_t
qm_gb_list_find(array *lst, const depend_atom *x)
{
	size_t       n;
	depend_atom *a;

	if (lst == NULL)
		return -1;
	array_for_each(lst, n, a) {
		if (strcmp(a->PN, x->PN) != 0)
			continue;
		if ((a->CATEGORY == NULL) != (x->CATEGORY == NULL) ||
				(a->CATEGORY != NULL &&
				 strcmp(a->CATEGORY, x->CATEGORY) != 0))
			continue;
		if ((a->SLOT == NULL) != (x->SLOT == NULL) ||
				(a->SLOT != NULL && strcmp(a->SLOT, x->SLOT) != 0))
			continue;
		return (ssize_t)n;
	}
	return -1;
}

/* drop atoms of lst that exactly appear in against */
static void
qm_gb_conflict_prune(array *lst, array *against, const char *what,
					 const char *by, const char *rname)
{
	size_t i;

	if (lst == NULL || against == NULL)
		return;
	for (i = array_cnt(lst); i > 0; ) {
		i--;
		depend_atom *x = array_get(lst, i);

		if (qm_gb_list_find(against, x) < 0)
			continue;
		warn("[%s] %s atom %s is overridden by %s", rname, what,
			 atom_to_string(x), by);
		array_delete(lst, i, atom_implode_cb);
	}
}

/* atoms in both lists cancel out and are dropped from both
*/
static void
qm_gb_mutual_prune(array *ex, array *in, const char *where)
{
	size_t i;

	if (ex == NULL || in == NULL)
		return;
	for (i = array_cnt(ex); i > 0; ) {
		i--;
		depend_atom *x = array_get(ex, i);
		ssize_t      j = qm_gb_list_find(in, x);

		if (j < 0)
			continue;
		warn("%s: %s appears in both the exclude and include list, "
			 "ignored in both", where, atom_to_string(x));
		array_delete(in, (size_t)j, atom_implode_cb);
		array_delete(ex, i, atom_implode_cb);
	}
}

/* name/slot match of a candidate against a filter list, same semantics
 * as qm_atom_excluded */
static bool
qm_gb_list_match(array *lst, const depend_atom *pa)
{
	size_t       n;
	depend_atom *x;

	if (lst == NULL || pa == NULL || pa->PN == NULL)
		return false;
	array_for_each(lst, n, x) {
		if (strcmp(x->PN, pa->PN) != 0)
			continue;
		if (x->CATEGORY != NULL && pa->CATEGORY != NULL &&
				strcmp(x->CATEGORY, pa->CATEGORY) != 0)
			continue;
		if (x->SLOT != NULL && pa->SLOT != NULL &&
				strcmp(x->SLOT, pa->SLOT) != 0)
			continue;
		return true;
	}
	return false;
}

/* -------- multi-binhost support (portage binrepos.conf parity) -----
 * repos come from /usr/share/portage/config/binrepos.conf, then
 * ${PORTAGE_CONFIGROOT}/etc/portage/binrepos.conf ([name] sections
 * with sync-uri = and optional priority =), and PORTAGE_BINHOST
 * entries are folded in as implicit repos, exactly like portage's
 * lib/portage/binrepo/config.py.
 * fetch() then scans the repos in (priority, name) order,
 * first successful download wins. */
struct qm_binrepo {
	char *name;
	char *uri;
	/* explicit location = from binrepos.conf, or NULL */
	char *loc;
	int   priority;
	/* verify-signature =: 1 true, 0 false, -1 unset */
	int   verify_sig;
	/* frozen =: the cached index is served forever, never refetched */
	int   frozen;
	/* getbinpkg-exclude/-include = atom lists, NULL when unset */
	array *gb_excl;
	array *gb_incl;
	/* xpak-skip warning shown once per repo */
	bool  xpak_warned;
};
static struct qm_binrepo *qm_binrepos  = NULL;
static size_t             qm_nbinrepos = 0;
/* candidate-selection scan order by (priority, name). storage order is
 * untouched, @local stays at index 0 */
static size_t            *qm_walk_order = NULL;

/* priority scale: 1 is the top, larger sinks lower; 0 is reserved for
 * the emergency store, reachable only through an explicit @name
 * selector; the local store defaults below every configured binhost */
#define QM_PRIO_LOWEST (1 << 30)

static void
binrepos_add(const char *name, const char *uri, const char *loc, int priority,
			 int verify_sig, int frozen, const char *gbex, const char *gbin)
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
	qm_binrepos[qm_nbinrepos].loc      = NULL;
	if (loc != NULL && *loc != '\0') {
		char *l = xstrdup(loc);

		len = strlen(l);
		while (len > 1 && l[len - 1] == '/')
			l[--len] = '\0';
		qm_binrepos[qm_nbinrepos].loc = l;
	}
	qm_binrepos[qm_nbinrepos].priority = priority;
	qm_binrepos[qm_nbinrepos].verify_sig = verify_sig;
	qm_binrepos[qm_nbinrepos].frozen  = frozen;
	qm_binrepos[qm_nbinrepos].gb_excl = NULL;
	qm_binrepos[qm_nbinrepos].gb_incl = NULL;
	qm_binrepos[qm_nbinrepos].xpak_warned = false;
	if (gbex != NULL && *gbex != '\0') {
		char src[192];

		snprintf(src, sizeof(src),
				 "binrepos.conf [%s] getbinpkg-exclude", name);
		qm_parse_gb_atoms(&qm_binrepos[qm_nbinrepos].gb_excl, gbex, src);
	}
	if (gbin != NULL && *gbin != '\0') {
		char src[192];

		snprintf(src, sizeof(src),
				 "binrepos.conf [%s] getbinpkg-include", name);
		qm_parse_gb_atoms(&qm_binrepos[qm_nbinrepos].gb_incl, gbin, src);
	}
	{
		char where[160];

		snprintf(where, sizeof(where), "binrepo [%s]", name);
		qm_gb_mutual_prune(qm_binrepos[qm_nbinrepos].gb_excl,
						   qm_binrepos[qm_nbinrepos].gb_incl, where);
	}
	qm_nbinrepos++;
}

/* effective store dir of repo i: explicit location = (or @local's
 * PKGDIR), else /var/cache/binhost/<name> (portage default when
 * PORTAGE_BINHOST is unset) */
static const char *
qm_repo_loc(size_t i, char *buf, size_t buflen)
{
	if (qm_binrepos[i].loc != NULL)
		return qm_binrepos[i].loc;
	snprintf(buf, buflen, "/var/cache/binhost/%s", qm_binrepos[i].name);
	return buf;
}

static void
qm_binrepos_flush(void *ctx, const char *name, const char *uri,
				  const char *loc, int priority, int verify_sig,
				  int frozen, const char *gbex, const char *gbin)
{
	(void)ctx;
	if (strcmp(name, "DEFAULT") == 0)
		return;
	if (uri[0] == '\0') {
		warn("binrepo %s has no sync-uri, ignored", name);
		return;
	}
	binrepos_add(name, uri, loc, priority, verify_sig, frozen, gbex, gbin);
}

static void
binrepos_load_file(const char *file)
{
	FILE *fp = fopen(file, "r");

	if (fp == NULL)
		return;
	binrepos_parse(fp, qm_binrepos_flush, NULL);
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

/* orders prebuilt binary repos by (priority, name). priority 1 first, QM_PRIO_LOWEST last.*/
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
	 * with incrementing priority (after explicit default 1) */
	prio = 1;
	bh = xstrdup(binhost);
	/* count and iterate in reverse like portage does */
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
			binrepos_add(iname, uris[n], NULL, prio, -1, 0, NULL, NULL);
		}
		free(uris);
	}
	free(bh);

	if (qm_nbinrepos > 1)
		qsort(qm_binrepos, qm_nbinrepos, sizeof(*qm_binrepos),
			  binrepos_cmp);

	/* PKGDIR == local store in our case.
	 * in portage case, they're both unset and have no
	 * real collision with each other, but in multibinhost
	 * case they would need to have a collisionary conflict. */
	{
		char   npkg[_Q_PATH_MAX];
		size_t nlen;
		size_t i;

		snprintf(npkg, sizeof(npkg), "%s", pkgdir);
		nlen = strlen(npkg);
		while (nlen > 1 && npkg[nlen - 1] == '/')
			npkg[--nlen] = '\0';

		for (i = 0; i < qm_nbinrepos; i++) {
			if (qm_binrepos[i].loc == NULL ||
					strcmp(qm_binrepos[i].loc, npkg) != 0)
				continue;
			warn("binrepo '%s': location = PKGDIR conflicts with the "
				 "local store; using /var/cache/binhost/%s instead",
				 qm_binrepos[i].name, qm_binrepos[i].name);
			free(qm_binrepos[i].loc);
			qm_binrepos[i].loc = NULL;
		}

		/* by default the LOWEST scan priority (QMERGE_LOCAL_PRIORITY overrides,
		 * 0 makes itthe emergency store):
		 * a distinct repo with no uri (never fetched), holding locally-
		 * built binpkgs; its index is (re)generated only by
		 * `qmerge -i`.This replaces the old qm_repo_loc i==0->pkgdir
		 * aliasing that conflated the local store with the top-
		 * priority binhost. */
		qm_binrepos = xrealloc(qm_binrepos,
							   sizeof(*qm_binrepos) * (qm_nbinrepos + 1));
		memmove(&qm_binrepos[1], &qm_binrepos[0],
				sizeof(*qm_binrepos) * qm_nbinrepos);
		qm_binrepos[0].name       = xstrdup("@local");
		qm_binrepos[0].uri        = NULL;
		qm_binrepos[0].loc        = xstrdup(npkg);
		if (qmerge_local_priority_conf != NULL &&
				qmerge_local_priority_conf[0] != '\0')
			qm_binrepos[0].priority = atoi(qmerge_local_priority_conf);
		else
			qm_binrepos[0].priority = QM_PRIO_LOWEST;
		qm_binrepos[0].verify_sig = -1;
		qm_binrepos[0].frozen     = 0;
		qm_binrepos[0].gb_excl    = NULL;
		qm_binrepos[0].gb_incl    = NULL;
		qm_binrepos[0].xpak_warned = false;
		qm_nbinrepos++;

		{
			size_t wi, wj;

			qm_walk_order = xrealloc(qm_walk_order,
					sizeof(*qm_walk_order) * qm_nbinrepos);
			for (wi = 0; wi < qm_nbinrepos; wi++)
				qm_walk_order[wi] = wi;
			for (wi = 1; wi < qm_nbinrepos; wi++)
				for (wj = wi; wj > 0 &&
						binrepos_cmp(&qm_binrepos[qm_walk_order[wj - 1]],
									 &qm_binrepos[qm_walk_order[wj]]) > 0;
						wj--)
				{
					size_t t = qm_walk_order[wj];

					qm_walk_order[wj] = qm_walk_order[wj - 1];
					qm_walk_order[wj - 1] = t;
				}
		}
	}

	/* the CLI include overrides conflicting conf exclude atoms per repo
	 * and vice versa (bintree.py:1436-1469) */
	{
		size_t i;

		for (i = 1; i < qm_nbinrepos; i++) {
			qm_gb_conflict_prune(qm_binrepos[i].gb_excl, qm_gb_incl_cli,
								 "getbinpkg-exclude", "--getbinpkg-include",
								 qm_binrepos[i].name);
			qm_gb_conflict_prune(qm_binrepos[i].gb_incl, qm_gb_excl_cli,
								 "getbinpkg-include", "--getbinpkg-exclude",
								 qm_binrepos[i].name);
		}
		qm_gb_mutual_prune(qm_gb_excl_cli, qm_gb_incl_cli,
						   "--getbinpkg-exclude/--getbinpkg-include");
	}
}

/* signatures are mandatory somewhere this run. FEATURES
 * binpkg-request-signature, or any binrepo with verify-signature=true;
 * binpkg-ignore-signature has prio over everything. */
static bool
qm_sigs_mandatory(void)
{
	static int cached = -1;
	size_t     i;

	if (cached >= 0)
		return cached != 0;
	cached = 0;
	if (contains_set("binpkg-ignore-signature", features) != NULL)
		return false;
	if (contains_set("binpkg-request-signature", features) != NULL) {
		cached = 1;
		return true;
	}
	binrepos_load();
	for (i = 0; i < qm_nbinrepos; i++)
		if (qm_binrepos[i].verify_sig == 1) {
			cached = 1;
			return true;
		}
	return false;
}

/* the FEATURES-only variant checks and limits the local store */
static bool
qm_sigs_requested(void)
{
	return contains_set("binpkg-ignore-signature", features) == NULL &&
		   contains_set("binpkg-request-signature", features) != NULL;
}

/* GLEP 78 gpkg by index PATH/file suffix */
static bool
qm_path_is_gpkg(const char *path)
{
	size_t l = path != NULL ? strlen(path) : 0;

	return l >= 9 && strcmp(path + l - 9, ".gpkg.tar") == 0;
}

/* under mandatory signatures only gpkg can satisfy: xpak has no
 * signature slot at all.. */
static void
qm_xpak_skip_warn(ssize_t ri)
{
	static bool bare_warned = false;

	if (ri < 0 || qm_nbinrepos == 0) {
		if (!bare_warned)
			warn("xpak packages in PKGDIR are ignored: signatures are "
				 "mandatory and only gpkg can carry them");
		bare_warned = true;
		return;
	}
	if (qm_binrepos[ri].xpak_warned)
		return;
	qm_binrepos[ri].xpak_warned = true;
	warn("[%s] xpak packages are ignored: signatures are mandatory and "
		 "only gpkg can carry them", qm_binrepos[ri].name);
}

/* per-repo getbinpkg-exclude/-include checks*/
static bool
qm_repo_pkg_allowed(size_t ri, const depend_atom *pa)
{
	bool have_incl;

	if (qm_nbinrepos == 0 || ri == 0)
		return true;
	if (qm_gb_list_match(qm_binrepos[ri].gb_excl, pa) ||
			qm_gb_list_match(qm_gb_excl_cli, pa))
		return false;
	have_incl = (qm_binrepos[ri].gb_incl != NULL &&
				 array_cnt(qm_binrepos[ri].gb_incl) > 0) ||
				(qm_gb_incl_cli != NULL && array_cnt(qm_gb_incl_cli) > 0);
	if (have_incl &&
			!qm_gb_list_match(qm_binrepos[ri].gb_incl, pa) &&
			!qm_gb_list_match(qm_gb_incl_cli, pa))
		return false;
	return true;
}

/* the Moves history is the remote maintainer's sole responsibility
 * and must be append-only.
 * we must flag a fetched file that lost directives the cached copy still
 * carries.
 * (behaviour is unchanged, the fetched file still replaces the cache) */
static void
qm_moves_shrink_warn(const char *fetched, const char *sdir, const char *rname)
{
	char   *dst  = NULL;
	char   *cbuf = NULL;
	size_t  clen = 0;
	char   *fbuf = NULL;
	size_t  flen = 0;
	char   *cur;
	char   *line;
	char   *sp;
	set    *fset;
	size_t  shrunk = 0;

	xasprintf(&dst, "%s/Moves", sdir);
	if (!eat_file(dst, &cbuf, &clen) || cbuf == NULL || cbuf[0] == '\0') {
		free(cbuf);
		free(dst);
		return;
	}
	if (!eat_file(fetched, &fbuf, &flen) || fbuf == NULL) {
		free(cbuf);
		free(dst);
		return;
	}

	fset = create_set();
	cur = xstrdup(fbuf);
	for (line = strtok_r(cur, "\r\n", &sp);
		 line != NULL;
		 line = strtok_r(NULL, "\r\n", &sp))
		if (*line != '\0')
			fset = add_set_unique(line, fset, NULL);
	free(cur);

	cur = xstrdup(cbuf);
	for (line = strtok_r(cur, "\r\n", &sp);
		 line != NULL;
		 line = strtok_r(NULL, "\r\n", &sp))
		if (*line != '\0' && !contains_set(line, fset))
			shrunk++;
	free(cur);

	if (shrunk > 0)
		warn("binhost %s: fetched Moves lost %zu directive%s still "
			 "present in the cached copy; Moves history is append-only "
			 "and must never be pruned on the binhost",
			 rname, shrunk, shrunk == 1 ? "" : "s");

	free_set(fset);
	free(fbuf);
	free(cbuf);
	free(dst);
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
			continue;
		*w++ = *r;
	}
	*w = '\0';
	return out;
}

/* If-Modified-Since threshold for the next fetch (0 = off) and the
 * matching 304-not-modified out-flag */
static time_t qm_fetch_ims    = 0;
/* metadata fetch (Packages/Moves/News.tar): these are cache files the
 * resolver needs, so they download for real even under --pretend, like
 * portage refreshing its binhost cache during a pretend run */
static bool   qm_fetch_meta   = false;
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

	if (pretend && !qm_fetch_meta) {
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
	curl_easy_setopt(curl, CURLOPT_MAXREDIRS, 10L);
	curl_easy_setopt(curl, CURLOPT_REDIR_PROTOCOLS_STR, "http,https");
	curl_easy_setopt(curl, CURLOPT_FAILONERROR, 1L);
	curl_easy_setopt(curl, CURLOPT_RESUME_FROM_LARGE, resume_from);
	curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, 60L);
	curl_easy_setopt(curl, CURLOPT_USERAGENT,
					 "portage-utils qmerge binpkg-fetch");
	curl_easy_setopt(curl, CURLOPT_NOPROGRESS,
					 (quiet || !verbose) ? 1L : 0L);
	/* index refresh: only download when newer than the cached copy.
	 * this needs a little more documentation, since the whole
	 * thing with Moves/News extra will probably confuse portage
	 * devs. */
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
			res = CURLE_OK;
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

/* time to harden the shells.
 * apparently they spike us pretty hard. */
static char *
shell_squote(const char *s)
{
	const char *p;
	char       *out;
	char       *q;
	size_t      n = 0;

	for (p = s; *p != '\0'; p++)
		n += (*p == '\'') ? 4 : 1;
	q = out = xmalloc(n + 1);
	for (p = s; *p != '\0'; p++) {
		if (*p == '\'') {
			*q++ = '\'';
			*q++ = '\\';
			*q++ = '\'';
			*q++ = '\'';
		} else {
			*q++ = *p;
		}
	}
	*q = '\0';
	return out;
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

	if (uri == NULL || *uri == '\0')
		return -1;

	fflush(NULL);

	base = strrchr(src, '/');
	base = base != NULL ? base + 1 : src;
	xasprintf(&dest, "%s/%s", destdir, base);

	if (qfetchcommand[0] != '\0') {
		/* qmerge-specific fetcher: when QFETCHCOMMAND is set in
		 * make.conf/env, spawn it (same portage template grammar:
		 * ${DISTDIR} ${URI} ${FILE}), exporting the vars it refers
		 * to; failures are tolerated so the next repo can be tried.
		 * Empty (the default) -> built-in libcurl.
		 * Deliberately NOT portage's FETCHCOMMAND,
		 * so make.globals' wget default does not drag wget in. */
		char *cmd;
		char *script;

		if (qresumecommand[0] != '\0' &&
				stat(dest, &st) == 0 && st.st_size > 0)
			cmd = unescape_fetchcommand(qresumecommand);
		else
			cmd = unescape_fetchcommand(qfetchcommand);

		/* shell-quote the exported values correction */
		char *e_dd   = shell_squote(destdir);
		char *e_uri  = shell_squote(uri);
		char *e_src  = shell_squote(src);
		char *e_base = shell_squote(base);

		xasprintf(&script,
				"(export DISTDIR='%s' URI='%s/%s' FILE='%s'; %s%s) || :",
				e_dd, e_uri, e_src, e_base,
				pretend ? "echo " : "", cmd);
		xsystem(script, AT_FDCWD);
		free(e_dd);
		free(e_uri);
		free(e_src);
		free(e_base);
		free(script);
		free(cmd);
	} else {
		/* no external fetch tool configured: built-in libcurl */
		(void)fetch_curl(uri, destdir, src);
	}

	if (stat(dest, &st) == 0 && st.st_size > 0) {
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
	{
		size_t remotes = 0;
		for (i = 0; i < qm_nbinrepos; i++)
			if (qm_binrepos[i].uri != NULL && qm_binrepos[i].uri[0] != '\0')
				remotes++;
		if (remotes == 0) {
			if (!warned) {
				warn("no binhosts configured "
					 "(binrepos.conf missing and PORTAGE_BINHOST unset)");
				warned = true;
			}
			return;
		}
	}

	base = strrchr(src, '/');
	base = base != NULL ? base + 1 : src;

	/* scan the repos in priority order until one delivers; the local
	 * store (no uri) can't serve downloads, fetch_repo skips it */
	for (i = 0; i < qm_nbinrepos; i++) {
		if (qm_binrepos[i].uri == NULL || qm_binrepos[i].uri[0] == '\0')
			continue;
		if (fetch_repo(i, destdir, src) == 0)
			break;

		/* show every candidate in fallback order */
		if (pretend)
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

/* bare -f -> an explicit refresh request: refetch the index in full,
 * no TTL shortcut, no If-Modified-Since, so a sync-uri change takes
 * effect right there */
static bool qm_index_force = false;

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

	/* -f: fetch */
	if (force_download == 1) {
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
		qm_fetch_meta = true;
		for (i = 0; i < qm_nbinrepos; i++) {
			const char *loc;
			char        spath[_Q_PATH_MAX + 16];
			struct stat sst;
			bool        fetched = false;

			if (qm_binrepos[i].uri == NULL || qm_binrepos[i].uri[0] == '\0')
				continue;

			loc = qm_repo_loc(i, locbuf, sizeof(locbuf));

			/* frozen repo: the cached index is served forever.
			 * an empty cache still fetches once */
			if (qm_binrepos[i].frozen) {
				snprintf(spath, sizeof(spath), "%s%s/%s",
						 portroot, loc, Packages);
				if (stat(spath, &sst) == 0 && sst.st_size > 0) {
					if (!quiet)
						printf(">>> Packages index from %s is frozen "
							   "(using cached copy)\n",
							   qm_binrepos[i].name);
					continue;
				}
			}

			/* a cached index younger than its TTL header is current.
			 * bare -f skips the shortcut, the refresh we needed */
			if (!qm_index_force && qm_index_fresh(loc)) {
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

			/* If-Modified-Since from the cached copy's fetch time.
			 * a forced refresh sends none, a 304 from a new sync-uri
			 * must not preserve the old catalog */
			snprintf(spath, sizeof(spath), "%s%s/%s",
					 portroot, loc, Packages);
			qm_fetch_ims = !qm_index_force && stat(spath, &sst) == 0
					? sst.st_mtime : 0;

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
				} else {
					warn("no Packages index from binhost %s, "
						 "keeping previous", qm_binrepos[i].name);
				}
				continue;
			}

			/* the store copy is a metadata cache, portage refreshes its
			 * binhost cache under --pretend too: without this a fresh
			 * box resolves against an empty (or stale) index.
			 * dropping !pretend */
			if (stat(Packages, &st) == 0 && st.st_size > 0) {
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
					qm_moves_policy() != QM_MV_REPO_ONLY && !pretend) {
				bool got = fetch_repo(i, buf, "Moves") == 0 &&
						stat("Moves", &st) == 0 && st.st_size > 0;

				if (got) {
					char *mdir;
					int   mdfd;
					int   msfd;

					xasprintf(&mdir, "%s%s", portroot, loc);
					if (mkdir_p(mdir, 0755) == 0 &&
							(mdfd = open(mdir, O_RDONLY | O_CLOEXEC)) >= 0) {
						qm_moves_shrink_warn("Moves", mdir,
											 qm_binrepos[i].name);
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
				} else {
					char       *mp;
					struct stat cst;

					xasprintf(&mp, "%s%s/Moves", portroot, loc);
					if (stat(mp, &cst) == 0 && cst.st_size > 0)
						warn("binhost %s no longer serves a Moves file; "
							 "keeping the cached copy (Moves history must "
							 "never be removed from the binhost)",
							 qm_binrepos[i].name);
					free(mp);
				}
			}
		}

		qm_fetch_meta = false;

		if (!pretend) {
			qm_apply_moves_all();
			qm_apply_news_all();
		}
	}

	free(buf);
}

static tree_ctx *qmerge_vdb_tree    = NULL;
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

/* warn when the local index exists but the store's contents
 * changed after it was written;
 * `qmerge -i' still overwrites it if invoked manually, same
 * as portage does */
static void
qm_local_index_freshness(const char *loc)
{
	static bool    done = false;
	char           path[_Q_PATH_MAX + 16];
	struct stat    ist;
	struct stat    dst;
	DIR           *d;
	struct dirent *de;
	size_t         i;
	bool           stale = false;

	if (done)
		return;
	done = true;

	for (i = 1; i < qm_nbinrepos; i++) {
		char        lb[_Q_PATH_MAX];
		const char *l = qm_repo_loc(i, lb, sizeof(lb));

		if (strcmp(l, loc) == 0)
			return;
	}

	snprintf(path, sizeof(path), "%s%s/%s", portroot, loc, Packages);
	if (stat(path, &ist) != 0)
		return;

	snprintf(path, sizeof(path), "%s%s", portroot, loc);
	if (stat(path, &dst) == 0 && dst.st_mtime > ist.st_mtime)
		stale = true;
	if (!stale && (d = opendir(path)) != NULL) {
		while (!stale && (de = readdir(d)) != NULL) {
			char sub[_Q_PATH_MAX + 300];

			if (de->d_name[0] == '.')
				continue;
			snprintf(sub, sizeof(sub), "%.4095s/%s", path, de->d_name);
			if (stat(sub, &dst) == 0 && S_ISDIR(dst.st_mode) &&
					dst.st_mtime > ist.st_mtime)
				stale = true;
		}
		closedir(d);
	}
	if (stale)
		warn("local binpkg index may be stale; run `qmerge -i'");
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

	if (i == 0)
		qm_local_index_freshness(loc);
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

/* --repos: emerge-info-style listing of the configured binhosts in
 * fallback (priority) order; -v adds the local store path.
 * we should have had these from the beginning*/
/* position of a repo in the priority scan */
static size_t
qm_repo_pos(size_t idx)
{
	size_t i;

	for (i = 0; i < qm_nbinrepos; i++)
		if (qm_walk_order[i] == idx)
			return i;
	return i;
}

static int
qm_print_repos(void)
{
	size_t i;

	binrepos_load();
	if (qm_nbinrepos == 0) {
		warn("no binhosts configured "
			 "(binrepos.conf missing and PORTAGE_BINHOST unset)");
		return EXIT_FAILURE;
	}
	printf("%sConfigured binhost repositories (priority order):%s\n",
		   GREEN, NORM);
	for (i = 0; i < qm_nbinrepos; i++) {
		size_t w = qm_walk_order[i];

		/* this would be the local pkgs store
		 * the one established in the PKGDIR, for now */
		if (qm_binrepos[w].uri == NULL) {
			printf("  %s%-16s%s (local)     %s%s%s%s\n",
				   MAGENTA, qm_binrepos[w].name, NORM,
				   DKBLUE, qm_binrepos[w].loc != NULL ?
						qm_binrepos[w].loc : pkgdir, NORM,
				   qm_binrepos[w].priority == 0 ?
						"  [emergency: @name only]" :
				   qm_binrepos[w].priority != QM_PRIO_LOWEST ?
						"  [priority raised]" : "");
			continue;
		}
		printf("  %s%-16s%s priority %-3d %s%s%s%s%s%s\n",
			   /* honestly would have liked a fuchsia here,
			    * but we don't want to break gentooes eyes */
			   MAGENTA, qm_binrepos[w].name, NORM,
			   qm_binrepos[w].priority,
			   DKBLUE, qm_binrepos[w].uri != NULL ?
					qm_binrepos[w].uri : "", NORM,
			   qm_binrepos[w].verify_sig == 1 ? "  [verify-signature]" :
			   qm_binrepos[w].verify_sig == 0 ? "  [unverified]" : "",
			   qm_binrepos[w].frozen ? "  [frozen]" : "",
			   qm_binrepos[w].priority == 0 ?
					"  [emergency: @name only]" : "");
		if (verbose) {
			char locbuf[_Q_PATH_MAX];

			printf("  %-16s store    %s\n", "",
				   qm_repo_loc(w, locbuf, sizeof(locbuf)));
			if (qm_binrepos[w].gb_excl != NULL &&
					array_cnt(qm_binrepos[w].gb_excl) > 0)
				printf("  %-16s getbinpkg-exclude: %zu atom(s)\n", "",
					   array_cnt(qm_binrepos[w].gb_excl));
			if (qm_binrepos[w].gb_incl != NULL &&
					array_cnt(qm_binrepos[w].gb_incl) > 0)
				printf("  %-16s getbinpkg-include: %zu atom(s)\n", "",
					   array_cnt(qm_binrepos[w].gb_incl));
		}
	}
	return EXIT_SUCCESS;
}

/* repo tag colour: 256-colour index 130, the closest palette entry to
 * sienna #a0522d. explicitly requested targets (emerge bolds its world
 * entries the same way). empty when the global colour state says no
 * colour */
static const char *
qm_repo_tag_color_b(bool boldtag)
{
	if (*NORM == '\0')
		return "";
	return boldtag ? "\033[01;38;5;130m" : "\033[38;5;130m";
}
#define qm_repo_tag_color() qm_repo_tag_color_b(false)

/* emerge's keyword column for the merge list: "" = stable for ARCH, "~" =
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
/* not yet supported */
#define BV_EBUILD    (1<<0)
#define BV_VDB       (1<<1)
#define BV_BINPKG    (1<<2)

/* is this cpv package.mask'd?  package_masks (profile cascade + /etc/portage)
 * is keyed by the raw mask-atom STRING, so index it once into cat/pn -> atoms
 * (like qkeyword does) and match the cpv against that pkg's mask atoms.
 * Empty(e.g. no profile on a pure binhost box) = never masked.
 * (package.unmask) override not yet parsed, deferred.)
 * cat/pn -> array of mask/unmask atoms; lazy */
static hash_t *binpkg_pmasks   = NULL;
static hash_t *binpkg_punmasks = NULL;

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

	if (binpkg_pmasks == NULL)
		binpkg_pmasks = binpkg_mask_index(package_masks);
	if (binpkg_punmasks == NULL)
		binpkg_punmasks = binpkg_mask_index(package_unmasks);

	bucket = hash_get(binpkg_pmasks, atom_format("%[CAT]%[PN]", patom));
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
	bucket = hash_get(binpkg_punmasks, atom_format("%[CAT]%[PN]", patom));
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
static int  qm_respect_use = -1;

/* --force-install: does exactly what you think it does.
 * but still won't pass over QMERGE_IGNORE_SLOT_CONFLICTS, that one will
 * be respected no matter what. */
static bool
qm_ignore_slot_conflicts(void)
{
	return getenv("QMERGE_IGNORE_SLOT_CONFLICTS") != NULL;
}

/* -F/--force install regardless of the soft candidate checks */
static bool
qm_force_soft(void)
{
	return force_download >= 2;
}

/* We're trying out a different architecuture here. There has to be a
 * force installation, but in the same time there's already a --nodeps
 * method which skips all the tests, and isn't picky with anything.
 * So the mixed solution here is to set a flag while resolving a user-named
 * target with -F, that target takes qm_force_pick flag instead of
 * already well-developd best_version, implicitly the soft-checks are
 * skipped. Dependency level > 0 and layer 2 "repairs" never get to this.*/
static bool qm_forcing_target = false;
static set *qm_force_targets = NULL;

/* --exclude/QMERGE_EXCLUDE (portage -X). Hold these atoms at installed and
 * drop them from the merge. */
static array *qm_exclude       = NULL;
static set   *qm_exclude_noted = NULL;

static void
qm_parse_exclude(const char *arg, const char *src)
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
		if (qm_exclude == NULL)
			qm_exclude = array_new();
		array_append(qm_exclude, a);
	}
	free(tmp);
}

static bool
qm_atom_excluded(const depend_atom *atom)
{
	size_t       n;
	depend_atom *x;

	if (qm_exclude == NULL || atom == NULL || atom->PN == NULL)
		return false;
	array_for_each(qm_exclude, n, x) {
		if (x->PN == NULL || strcmp(x->PN, atom->PN) != 0)
			continue;
		if (x->CATEGORY != NULL && atom->CATEGORY != NULL &&
				strcmp(x->CATEGORY, atom->CATEGORY) != 0)
			continue;
		if (x->SLOT != NULL && atom->SLOT != NULL &&
				strcmp(x->SLOT, atom->SLOT) != 0)
			continue;
		return true;
	}
	return false;
}

/* --usepkg-exclude: atoms never satisfied from binpkgs.
 * portage falls back to a source build for these.
 * qmerge has no ebuilds, so an atom only an excluded binpkg 
 * can satisfy refuses at resolve time. */
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
 * Packages).
 * Applied to VDB + world during -f; the applied content is
 * kept in <store>/.moves-applied so a directive set runs once.
 * a1 = move old cat/pn, or slotmove atom
 * a2 = move new cat/pn, or slotmove old slot
 * a3 = slotmove new slot */
/* the Moves-file parser (struct move / moves_parse / moves_free)
 * lives in libq/moves.c so it can be fuzzed on its own. */

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
 * collision with an existing entry under the new name = skip + warn.
 * mammoth of functions that have no architectural explanation bellow. */
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
	snprintf(oldcat, sizeof(oldcat), "%.*s",
			 (int)MIN((size_t)(s - oldcp), sizeof(oldcat) - 1), oldcp);
	snprintf(oldpn, sizeof(oldpn), "%s", s + 1);
	s = strchr(newcp, '/');
	snprintf(newcat, sizeof(newcat), "%.*s",
			 (int)MIN((size_t)(s - newcp), sizeof(newcat) - 1), newcp);
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
 * (runs even when oldcp itself is not installed: revdeps may still
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
 * one-shot; 
 * trusted = local repo data, exempt from the signature
 * posture that gates the fetched transport.
 * Returns -1 when skipped (unchanged/refused), else the number of VDB mutations. */
static int
qm_apply_moves_buf(const char *mbuf, const char *rname, const char *apath,
				   bool trusted)
{
	char           *abuf = NULL;
	size_t          alen = 0;
	array          *mv;
	size_t          mi;
	struct move *m;
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
	mv = moves_parse(mbuf);
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
	moves_free(mv);
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
 * applies on sync.
 * notice = mention outranked binhost Moves files */
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
		qm_moves_map = moves_parse(buf);
		free(buf);
	}
}

/* cannot-satisfy diagnostic: the atom is an endpoint of a known move */
static const char *
qm_move_fail_hint(const depend_atom *atom)
{
	static char     hint[320];
	size_t          i;
	struct move *m;
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
qm_emit_news(int dfd, const char *pdir)
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
	int            fd     = -1;
	bool           werr   = false;

	if ((!qnews_enable && !qm_news_force) || main_overlay == NULL)
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
				fd = dfd >= 0 ? openat(dfd, "News.tar",
						O_WRONLY | O_CREAT | O_TRUNC | O_NOFOLLOW | O_CLOEXEC,
						0644) : -1;
				if (fd < 0 ||
						archive_write_set_format_ustar(aw) != ARCHIVE_OK ||
						archive_write_open_fd(aw, fd) != ARCHIVE_OK) {
					warnp("cannot write %s", npath);
					archive_write_free(aw);
					aw = NULL;
					if (fd >= 0) {
						close(fd);
						if (dfd >= 0)
							unlinkat(dfd, "News.tar", 0);
					}
					fd = -1;
					werr = true;
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
			if (archive_write_header(aw, e) != ARCHIVE_OK ||
					archive_write_data(aw, fbuf, clen) !=
						(la_ssize_t)clen) {
				warnp("cannot write %s", npath);
				archive_entry_free(e);
				free(fbuf);
				free(fpath);
				werr = true;
				break;
			}
			archive_entry_free(e);
			free(fbuf);
			free(fpath);
		}
		closedir(id);
		free(idir);
		if (werr)
			break;
		items++;
	}
	closedir(d);
	if (aw != NULL) {
		if (archive_write_close(aw) != ARCHIVE_OK)
			werr = true;
		archive_write_free(aw);
		if (fd >= 0) {
			if (!werr)
				binpkg_perms_fd(fd, false);
			close(fd);
		}
		if (werr) {
			if (dfd >= 0)
				unlinkat(dfd, "News.tar", 0);
		} else
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

static bool
qm_news_mark_unread(const char *ndir, const char *repoid, const char *nid)
{
	static const char * const sufs[] = { "unread", "skip", NULL };
	size_t i;
	bool ok = true;

	for (i = 0; sufs[i] != NULL; i++) {
		char  p[_Q_PATH_MAX + 256];
		FILE *f;

		snprintf(p, sizeof(p), "%s/news-%s.%s", ndir, repoid, sufs[i]);
		f = fopen(p, "a");
		if (f == NULL) {
			ok = false;
			continue;
		}
		if (fprintf(f, "%s\n", nid) < 0)
			ok = false;
		if (fclose(f) != 0)
			ok = false;
		else
			chmod(p, 0644);
	}
	return ok;
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
				 (int)MIN((size_t)(p2 - p1 - 1),
						  sizeof(want) - 8), p1 + 1);
		if (strcmp(p2 + 1, want) != 0)
			continue;
		sz = archive_entry_size(e);
		if (sz <= 0 || sz > (la_int64_t)1024 * 1024)
			continue;
		body = xmalloc((size_t)sz + 1);
		if (archive_read_data(ar, body, (size_t)sz) != (la_ssize_t)sz) {
			free(body);
			continue;
		}
		body[sz] = '\0';
		if (qm_news_relevant(body)) {
			snprintf(key, sizeof(key), "%.*s",
				 (int)MIN((size_t)(p2 - nm), sizeof(key) - 1), nm);
			add_set(key, relevant);
		}
		free(body);
	}
	archive_read_free(ar);

	/* pass 2: cache bodies + unread/skip bookkeeping */
	bool apply_ok = true;
	snprintf(ndir, sizeof(ndir), "%svar/lib/gentoo/news", portroot);
	mkdir_p(ndir, 0755);
	ar = archive_read_new();
	archive_read_support_format_tar(ar);
	archive_read_support_filter_all(ar);
	if (archive_read_open_filename(ar, tpath, 65536) == ARCHIVE_OK) {
		int r;

		while ((r = archive_read_next_header(ar, &e)) == ARCHIVE_OK) {
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
			snprintf(key, sizeof(key), "%.*s",
				 (int)MIN((size_t)(p2 - nm), sizeof(key) - 1), nm);
			if (contains_set(key, relevant) == NULL)
				continue;
			snprintf(repoid, sizeof(repoid), "%.*s",
					 (int)MIN((size_t)(p1 - nm),
							  sizeof(repoid) - 1), nm);
			snprintf(nid, sizeof(nid), "%.*s",
					 (int)MIN((size_t)(p2 - p1 - 1),
							  sizeof(nid) - 1), p1 + 1);
			sz = archive_entry_size(e);
			if (sz < 0 || sz > (la_int64_t)1024 * 1024)
				continue;
			body = xmalloc((size_t)sz + 1);
			if (archive_read_data(ar, body, (size_t)sz) !=
					(la_ssize_t)sz) {
				free(body);
				apply_ok = false;
				continue;
			}
			snprintf(opath, sizeof(opath), "%s/items/%s/%s",
					 ndir, repoid, nid);
			mkdir_p(opath, 0755);
			snprintf(opath, sizeof(opath), "%s/items/%s/%s/%s",
					 ndir, repoid, nid, p2 + 1);
			f = fopen(opath, "w");
			if (f == NULL) {
				apply_ok = false;
			} else {
				if (fwrite(body, 1, (size_t)sz, f) != (size_t)sz)
					apply_ok = false;
				if (fclose(f) != 0)
					apply_ok = false;
				chmod(opath, 0644);
			}
			free(body);
			if (!qm_news_id_seen(ndir, repoid, nid)) {
				if (!qm_news_mark_unread(ndir, repoid, nid))
					apply_ok = false;
				fresh++;
			}
		}
		if (r != ARCHIVE_EOF)
			apply_ok = false;
		archive_read_free(ar);
	} else {
		apply_ok = false;
		archive_read_free(ar);
	}
	free_set(relevant);
	if (fresh > 0)
		qprintf("%s>>>%s %d new news item%s from %s\n",
				GREEN, NORM, fresh, fresh == 1 ? "" : "s", rname);
	if (apply_ok) {
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
 * <PKGDIR>/Moves next to Packages for repo-less eaters */
static void
qm_emit_moves(int dfd, const char *pdir)
{
	char  mpath[_Q_PATH_MAX + 8];
	char *content = qm_collect_updates();
	int   fd;
	FILE *out;

	if (content == NULL)
		return;
	snprintf(mpath, sizeof(mpath), "%s/Moves", pdir);
	fd = dfd >= 0 ? openat(dfd, "Moves",
			O_WRONLY | O_CREAT | O_TRUNC | O_NOFOLLOW | O_CLOEXEC, 0644) : -1;
	if (fd < 0 || (out = fdopen(fd, "w")) == NULL) {
		warnp("cannot write %s", mpath);
		if (fd >= 0)
			close(fd);
	} else {
		fputs(content, out);
		binpkg_perms_fd(fileno(out), false);
		fclose(out);
		qprintf("%s>>>%s wrote %s (%zu bytes)\n",
				GREEN, NORM, mpath, strlen(content));
	}
	free(content);
}

/* USE check rejections collected during resolution, keyed per pkgs
 * (cat/pn:slot -> reject lines), printed as aa portage-style "ignored
 * due to non matching USE" block with the merge list. Only packages where
 * NO instance survived the checks are shown, a accepted duplicate makes
 * the stale-instance rejects irrelevant (emerge NOTE behavior). */
static hash_t *qm_use_rejects = NULL;
static hash_t *qm_use_accepts = NULL;

static void
qm_use_gate_key(atom_ctx *patom, char *key, size_t keylen)
{
	if (patom->CATEGORY != NULL && patom->SLOT != NULL)
		snprintf(key, keylen, "%s/%s:%s",
				 patom->CATEGORY, patom->PN, patom->SLOT);
	else if (patom->CATEGORY != NULL)
		snprintf(key, keylen, "%s/%s", patom->CATEGORY, patom->PN);
	else
		snprintf(key, keylen, "%s", patom->PN);
}

static void
qm_use_reject_add(atom_ctx *patom, const char *msg)
{
	char  key[512];
	set  *d;

	qm_use_gate_key(patom, key, sizeof(key));
	if (qm_use_rejects == NULL)
		qm_use_rejects = hash_new();
	d = hash_get(qm_use_rejects, key);
	if (d == NULL) {
		d = create_set();
		hash_add(qm_use_rejects, key, d, NULL);
	}
	add_set_unique(msg, d, NULL);
}

static void
qm_use_accept_add(atom_ctx *patom)
{
	char  key[512];
	char  cpf[512];
	char *cur;

	qm_use_gate_key(patom, key, sizeof(key));
	snprintf(cpf, sizeof(cpf), "%s/%s",
			 patom->CATEGORY ? : "", patom->PF ? : "");
	if (qm_use_accepts == NULL)
		qm_use_accepts = hash_new();
	cur = hash_get(qm_use_accepts, key);
	if (cur == NULL) {
		qm_use_accepts = hash_add(qm_use_accepts, key,
								  xstrdup(cpf), NULL);
	} else if (atom_compare_str(cpf, cur) == NEWER) {
		void *prev = NULL;

		qm_use_accepts = hash_add(qm_use_accepts, key,
								  xstrdup(cpf), &prev);
		free(prev);
	}
}

static struct use_ctx *qm_uc(void);
static int qm_strcmp_cb(const void *l, const void *r);

/* binpkg-respect-use, adapted for a config without ebuilds: verify a
 * binpkg's built USE against the local configuration.The default
 * trust mode checks only flags with a strong signal, explicit USE
 * (make.conf/profiles), use.force (must be on) and use.mask (must be
 * off).
 * Strict mode (explicit --binpkg-respect-use=y) is emerge's
 * binpkg-respect-use: every IUSE flag's built state must equal the
 * wanted state, USE_EXPAND groups and package.use included. */
static bool
binpkg_use_ok_r(tree_pkg_ctx *pkg, atom_ctx *patom, const char *rname,
				bool strict, char *why, size_t whylen)
{
	char *iusestr = tree_pkg_meta(pkg, Q_IUSE);
	set  *built;
	char *tmp;
	char *tok;
	char *sp;
	bool  ok = true;

	if (iusestr == NULL || *iusestr == '\0') {
		if (why == NULL)
			qm_use_accept_add(patom);
		return true;
	}

	built = usedep_flags_to_set(tree_pkg_meta(pkg, Q_USE));
	tmp   = xstrdup(iusestr);
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		bool have;
		bool def_on;
		int  po;
		char msg[512];

		def_on = *tok == '+';
		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok == '\0')
			continue;

		have = contains_set(tok, built) != NULL;

		/* new feature, need docs*/
		if (strict) {
			bool want = uc_use_wanted(qm_uc(), patom, tok, def_on);

			if (have == want)
				continue;
			if (why != NULL) {
				if (want)
					snprintf(why, whylen,
							 "built without %s (config wants it)", tok);
				else
					snprintf(why, whylen,
							 "built with %s (config disables it)", tok);
			} else {
				if (want)
					snprintf(msg, sizeof(msg),
							 "=%s [%s] built without %s (config wants it)",
							 atom_to_string(patom),
							 rname != NULL ? rname : "?", tok);
				else
					snprintf(msg, sizeof(msg),
							 "=%s [%s] built with %s (config disables it)",
							 atom_to_string(patom),
							 rname != NULL ? rname : "?", tok);
				qm_use_reject_add(patom, msg);
			}
			ok = false;
			break;
		}

		/* package.use.mask/package.use.force override the global sets
		 * per package. this is how it should normally happen in a gentoo
		 * with portage as well, even if it's about prebuilt binary. */
		po = uc_pkg_flag_override(patom, tok, pkg_use_mask);
		if (po == 1 ||
				(po == -1 && use_mask != NULL &&
				 contains_set(tok, use_mask) != NULL)) {
			const char *msrc = po == 1 ? "package.use.mask" : "use.mask";

			if (have) {
				if (why != NULL) {
					snprintf(why, whylen,
							 "built with %s (%s disables it)", tok, msrc);
				} else {
					snprintf(msg, sizeof(msg),
							 "=%s [%s] built with %s (%s disables it)",
							 atom_to_string(patom),
							 rname != NULL ? rname : "?", tok, msrc);
					qm_use_reject_add(patom, msg);
				}
				ok = false;
				break;
			}
			continue;
		}
		po = uc_pkg_flag_override(patom, tok, pkg_use_force);
		if (po == 1 ||
				(po == -1 &&
				 ((use_force != NULL &&
				   contains_set(tok, use_force) != NULL) ||
				  (ev_use != NULL && contains_set(tok, ev_use) != NULL))))
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
					qm_use_reject_add(patom, msg);
				}
				ok = false;
				break;
			}
		}
	}
	free(tmp);
	free_set(built);
	if (why == NULL && ok)
		qm_use_accept_add(patom);
	return ok;
}
#define binpkg_use_ok(P,A,R,S) binpkg_use_ok_r(P, A, R, S, NULL, 0)

/* the USE/IUSE consacrated in libq/useflags.c (fuzzable in
 * isolation); qm_uc() hands them this run's config state.  qm_use_drift
 * is pure and needs no ctx. */
#define qm_use_drift(B, I) uc_use_drift(B, I)

/* resolution-time notices for explicit binhost selections and affinity
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
/* was the binpkg rebuilt vs the installed copy?  Same version,
 * BUILD_TIME differs, emerge --rebuilt-binaries detection
 * (depgraph.py rebuilt_binaries branch). */
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
	if (bt == NULL || *bt == '\0')
		return false;
	b = strtoull(bt, NULL, 10);
	if (b == 0)
		return false;
	it = tree_pkg_meta(inst, Q_BUILD_TIME);
	iv = (it != NULL && *it != '\0') ? strtoull(it, NULL, 10) : 0;
	if (qm_rebuilt_ts_set)
		return b > iv && b >= qm_rebuilt_ts;
	return b != iv;
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

/* the USE/IUSE evaluators (qm_expand_group/qm_pkg_flag_override/
 * qm_use_wanted/qm_use_mismatch) propelled in libq/useflags.c; qmerge calls
 * them through qm_uc(), which points a shared use_ctx at this run's
 * config globals. */
static struct use_ctx qm_uctx;

static struct use_ctx *
qm_uc(void)
{
	qm_uctx.ev_use              = ev_use;
	qm_uctx.ev_use_neg          = ev_use_neg;
	qm_uctx.use_mask            = use_mask;
	qm_uctx.use_force           = use_force;
	qm_uctx.pkg_use             = pkg_use;
	qm_uctx.pkg_use_force       = pkg_use_force;
	qm_uctx.pkg_use_mask        = pkg_use_mask;
	qm_uctx.all_config_vars     = all_config_vars;
	qm_uctx.use_expand          = use_expand;
	qm_uctx.use_expand_implicit = use_expand_implicit;
	qm_uctx.use_expand_hidden   = use_expand_hidden;
	return &qm_uctx;
}

#define qm_use_mismatch(P)           uc_use_mismatch(qm_uc(), P)
#define qm_expand_group(T, S)        uc_expand_group(qm_uc(), T, S)
#define qm_expand_group_hidden(V)    uc_expand_group_hidden(qm_uc(), V)
#define qm_pkg_flag_override(A, T, L) uc_pkg_flag_override(A, T, L)

/* Finally, the FEATURES=preserve-libs clone from Portage.
 * Registry preservation of ABI-bumped libraries still NEEDed by installed packages.
 * Portage preserved_libs_registry byte-format shared with a portage on the same
 * machine.
 * Users upgrade/bump/install via @preserved-rebuild (this would be remote binhost re-merges).
 * A (our) GC after merge/unmerge drops entries whose last NEEDing package left. */
static preserved_reg *qm_preserved_reg = NULL;

static bool
qm_preserve_active(void)
{
	return contains_set("preserve-libs", features) != NULL;
}

static preserved_reg *
qm_preserved_get(void)
{
	if (qm_preserved_reg == NULL) {
		char *f;

		xasprintf(&f, "%svar/lib/portage/preserved_libs_registry",
				  portroot);
		qm_preserved_reg = preserved_open(f);
		free(f);
		preserved_prune(qm_preserved_reg, portroot);
	}
	return qm_preserved_reg;
}

static void
qm_preserved_finish(void)
{
	if (qm_preserved_reg == NULL)
		return;
	if (!pretend)
		preserved_store(qm_preserved_reg);
	preserved_close(qm_preserved_reg);
	qm_preserved_reg = NULL;
}

static int
qm_linkage_cb(tree_pkg_ctx *pkg, void *priv)
{
	linkage_map *map = priv;
	atom_ctx    *a   = tree_pkg_atom(pkg, false);
	char         path[_Q_PATH_MAX];
	char         cpv[512];
	char        *buf = NULL;
	size_t       len = 0;

	if (a == NULL || a->CATEGORY == NULL || a->PF == NULL)
		return 0;
	snprintf(cpv, sizeof(cpv), "%s/%s", a->CATEGORY, a->PF);
	snprintf(path, sizeof(path), "%s%s/%s/%s/NEEDED.ELF.2",
			 portroot, portvdb, a->CATEGORY, a->PF);
	if (eat_file(path, &buf, &len) && buf != NULL && buf[0] != '\0')
		linkage_add_pkg(map, cpv, buf);
	free(buf);
	return 0;
}

static linkage_map *
qm_linkage_build(void)
{
	linkage_map *map = linkage_new();
	tree_ctx    *vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);

	if (vdb != NULL) {
		tree_foreach_pkg_fast(vdb, qm_linkage_cb, map, NULL);
		tree_close(vdb);
	}
	return map;
}

/* GLEP 74 REQUIRES/PROVIDES blobs, "arch: soname soname ..." lines */
static bool
qm_soname_in(const char *blob, const char *cat, const char *soname)
{
	const char *p    = blob;
	size_t      slen = strlen(soname);
	bool        want = cat == NULL;

	while (p != NULL && *p != '\0') {
		const char *e;
		size_t      len;

		while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r')
			p++;
		if (*p == '\0')
			break;
		e = p;
		while (*e != '\0' && *e != ' ' && *e != '\t' &&
				*e != '\n' && *e != '\r')
			e++;
		len = (size_t)(e - p);
		if (p[len - 1] == ':') {
			if (cat != NULL)
				want = len - 1 == strlen(cat) &&
					strncmp(p, cat, len - 1) == 0;
		} else if (want && len == slen &&
				memcmp(p, soname, slen) == 0) {
			return true;
		}
		p = e;
	}
	return false;
}

static void
qm_preserve_add(array *out, set *keep, const char *path)
{
	size_t  i;
	char   *p;

	array_for_each(out, i, p)
		if (strcmp(p, path) == 0)
			return;
	array_append(out, xstrdup(path));
	if (keep != NULL)
		add_set(path, keep);
	if (!quiet)
		printf("%s>>>%s needed    %s\n", GREEN, NORM, path);
}

/* soname still NEEDed by a package that is neither replaced nor the
 * replacement, and the incoming package does not provide it.
 * The soname symlink is preserved along with the real file. */
static array *
qm_preserve_compute(array *members, tree_pkg_ctx *newpkg, set *keep)
{
	array        *out = array_new();
	linkage_map  *map;
	char         *nprov;
	size_t        mi;
	tree_pkg_ctx *m;
	bool          haslibs = false;

	/* the VDB-wide list map can be built when a replaced
	 * package ships a library at all (a soname field in its
	 * NEEDED.ELF.2).
	 * can or if. */
	array_for_each(members, mi, m) {
		atom_ctx *ma = tree_pkg_atom(m, false);
		char      npath[_Q_PATH_MAX];
		char     *nbuf = NULL;
		size_t    nlen = 0;

		if (ma == NULL || ma->CATEGORY == NULL || ma->PF == NULL)
			continue;
		snprintf(npath, sizeof(npath), "%s%s/%s/%s/NEEDED.ELF.2",
				 portroot, portvdb, ma->CATEGORY, ma->PF);
		if (eat_file(npath, &nbuf, &nlen) && nbuf != NULL) {
			char *ln = nbuf;

			while (*ln != '\0' && !haslibs) {
				char *semi1 = strchr(ln, ';');
				char *nl    = strchr(ln, '\n');

				if (semi1 != NULL && (nl == NULL || semi1 < nl) &&
						semi1[1] != '\0') {
					char *semi2 = strchr(semi1 + 1, ';');

					if (semi2 != NULL && (nl == NULL || semi2 < nl) &&
							semi2[1] != ';' && semi2[1] != '\0' &&
							semi2[1] != '\n')
						haslibs = true;
				}
				if (nl == NULL)
					break;
				ln = nl + 1;
			}
		}
		free(nbuf);
		if (haslibs)
			break;
	}
	if (!haslibs) {
		array_free(out);
		return NULL;
	}

	map   = qm_linkage_build();
	nprov = newpkg != NULL ? tree_pkg_meta(newpkg, Q_PROVIDES) : NULL;

	array_for_each(members, mi, m) {
		atom_ctx    *ma = tree_pkg_atom(m, false);
		char         mcpv[512];
		linkage_pkg *lp;
		linkage_obj *lo;
		size_t       oi;
		set         *syms = NULL;

		if (ma == NULL || ma->CATEGORY == NULL || ma->PF == NULL)
			continue;
		snprintf(mcpv, sizeof(mcpv), "%s/%s", ma->CATEGORY, ma->PF);
		lp = linkage_get(map, mcpv);
		if (lp == NULL)
			continue;
		array_for_each(lp->objs, oi, lo) {
			array *cons;
			size_t ci;
			char  *cc;
			bool   ext = false;

			if (lo->soname[0] == '\0')
				continue;
			if (keep != NULL &&
					contains_set(lo->path, keep) != NULL)
				continue;
			if (nprov != NULL &&
					qm_soname_in(nprov, lo->cat, lo->soname))
				continue;
			cons = linkage_revdeps(map, lo->cat, lo->soname, mcpv);
			array_for_each(cons, ci, cc) {
				size_t        si;
				tree_pkg_ctx *sm;
				bool          isrepl = false;

				array_for_each(members, si, sm) {
					atom_ctx *sa = tree_pkg_atom(sm, false);
					char      scpv[512];

					snprintf(scpv, sizeof(scpv), "%s/%s",
							 sa->CATEGORY ? : "", sa->PF ? : "");
					if (strcmp(scpv, cc) == 0) {
						isrepl = true;
						break;
					}
				}
				if (!isrepl) {
					ext = true;
					break;
				}
			}
			array_deepfree(cons, free);
			if (!ext)
				continue;
			if (syms == NULL) {
				char *cnt = tree_pkg_meta(m, Q_CONTENTS);

				syms = create_set();
				if (cnt != NULL) {
					char *ctmp = xstrdup(cnt);
					char *ln;
					char *csave;

					for (ln = strtok_r(ctmp, "\n", &csave);
						 ln != NULL;
						 ln = strtok_r(NULL, "\n", &csave)) {
						contents_entry *e = contents_parse_line(ln);

						if (e != NULL && e->type == CONTENTS_SYM)
							add_set(e->name, syms);
					}
					free(ctmp);
				}
			}
			qm_preserve_add(out, keep, lo->path);
			{
				char  lnk[_Q_PATH_MAX];
				char *sl = strrchr(lo->path, '/');

				if (sl != NULL) {
					snprintf(lnk, sizeof(lnk), "%.*s/%s",
							 (int)MIN((size_t)(sl - lo->path),
									  sizeof(lnk) - 1), lo->path,
							 lo->soname);
					if (strcmp(lnk, lo->path) != 0 &&
							contains_set(lnk, syms) != NULL)
						qm_preserve_add(out, keep, lnk);
				}
			}
		}
		if (syms != NULL)
			free_set(syms);
	}
	linkage_free(map);
	if (array_cnt(out) == 0) {
		array_free(out);
		out = NULL;
	}
	return out;
}

/* drop registry entries whose sonames no installed package NEEDs any
 * more, removing the preserved files themselves */
static void
qm_preserved_gc(void)
{
	preserved_reg *reg;
	linkage_map   *map;
	size_t         i;

	if (pretend)
		return;
	reg = qm_preserved_get();
	if (preserved_count(reg) == 0)
		return;
	map = qm_linkage_build();
	i = 0;
	while (i < preserved_count(reg)) {
		preserved_entry *pe     = array_get(preserved_entries(reg), i);
		bool             needed = false;
		size_t           n;
		char            *pt;

		array_for_each(pe->paths, n, pt) {
			const char *bn = strrchr(pt, '/');
			array      *cons;

			bn   = bn != NULL ? bn + 1 : pt;
			cons = linkage_revdeps(map, NULL, bn, NULL);
			needed = array_cnt(cons) > 0;
			array_deepfree(cons, free);
			if (needed)
				break;
		}
		if (needed) {
			i++;
			continue;
		}
		array_for_each(pe->paths, n, pt) {
			char *abs;

			xasprintf(&abs, "%s%s", portroot,
					  pt[0] == '/' ? pt + 1 : pt);
			if (unlink(abs) == 0)
				qprintf("%s<<<%s %s (preserved, no longer NEEDed)\n",
						GREEN, NORM, pt);
			free(abs);
		}
		{
			char *sl = strchr(pe->cps, ':');

			preserved_register(reg, pe->cpv,
							   sl != NULL ? sl + 1 : "0",
							   pe->counter, NULL);
		}
	}
	linkage_free(map);
}

/* emerge's localized_size: KiB rounded up, comma-grouped */
static void
qm_fmt_kib(char *out, size_t outlen, unsigned long long bytes)
{
	char               raw[32];
	size_t             rl;
	size_t             oi = 0;
	size_t             i;
	unsigned long long kib = (bytes + 1023) / 1024;

	snprintf(raw, sizeof(raw), "%llu", kib);
	rl = strlen(raw);
	for (i = 0; i < rl && oi + 2 < outlen; i++) {
		if (i > 0 && (rl - i) % 3 == 0)
			out[oi++] = ',';
		out[oi++] = raw[i];
	}
	out[oi] = '\0';
}

struct qm_uvflag {
	char *nm;
	bool  par;
};

struct qm_uvgrp {
	char  *var;
	array *en;
	array *dis;
};

static int
qm_uvflag_cmp(const void *a, const void *b)
{
	const struct qm_uvflag *fa = *(const struct qm_uvflag * const *)a;
	const struct qm_uvflag *fb = *(const struct qm_uvflag * const *)b;

	return strcmp(fa->nm, fb->nm);
}

static int
qm_uvgrp_cmp(const void *a, const void *b)
{
	const struct qm_uvgrp *ga = *(const struct qm_uvgrp * const *)a;
	const struct qm_uvgrp *gb = *(const struct qm_uvgrp * const *)b;
	bool ua = strcmp(ga->var, "USE") == 0;
	bool ub = strcmp(gb->var, "USE") == 0;

	if (ua != ub)
		return ua ? -1 : 1;
	return strcmp(ga->var, gb->var);
}

/* -v merge-lists annotation, emerge's per-package flag display: over the
 * binpkg's IUSE, enabled red / disabled blue, parens for
 * use.mask/use.force'd flags (not user-toggleable).
 * USE_EXPAND groups split out with the prefix stripped (hidden groups dropped),
 * members alpha-sorted enabled-block-then-disabled-block, then the
 * download size (0 for a store-cached gpkg), emerge-rounded */
static void
qm_print_use_verbose(tree_pkg_ctx *bpkg)
{
	char        *iusestr = tree_pkg_meta(bpkg, Q_IUSE);
	depend_atom *pa      = tree_pkg_atom(bpkg, true);
	set         *built;
	set         *seen    = create_set();
	array       *grps    = array_new();
	char        *tmp;
	char        *tok;
	char        *sp;
	size_t       gi;
	size_t       fi;
	struct qm_uvgrp  *g;
	struct qm_uvflag *f;

	built = usedep_flags_to_set(tree_pkg_meta(bpkg, Q_USE));
	tmp   = iusestr != NULL ? xstrdup(iusestr) : xstrdup("");
	for (tok = strtok_r(tmp, " \t\n", &sp);
		 tok != NULL;
		 tok = strtok_r(NULL, " \t\n", &sp))
	{
		const struct use_expand_pfx *ep;
		const char                 *sfx  = NULL;
		const char                 *gvar = "USE";
		const char                 *dnm;
		bool                        masked;
		bool                        forced;
		int                         o;

		if (*tok == '+' || *tok == '-')
			tok++;
		if (*tok == '\0' || contains_set(tok, seen) != NULL)
			continue;
		add_set_unique(tok, seen, NULL);

		ep = qm_expand_group(tok, &sfx);
		if (ep != NULL) {
			if (qm_expand_group_hidden(ep->var))
				continue;
			gvar = ep->var;
			dnm  = sfx;
		} else {
			dnm = tok;
		}

		o = qm_pkg_flag_override(pa, tok, pkg_use_mask);
		masked = o == 1 || (o == -1 &&
				use_mask != NULL && contains_set(tok, use_mask) != NULL);
		o = qm_pkg_flag_override(pa, tok, pkg_use_force);
		forced = o == 1 || (o == -1 &&
				use_force != NULL && contains_set(tok, use_force) != NULL);

		g = NULL;
		array_for_each(grps, gi, g) {
			if (strcmp(g->var, gvar) == 0)
				break;
			g = NULL;
		}
		if (g == NULL) {
			g = xmalloc(sizeof(*g));
			g->var = xstrdup(gvar);
			g->en  = array_new();
			g->dis = array_new();
			array_append(grps, g);
		}

		f = xmalloc(sizeof(*f));
		f->nm  = xstrdup(dnm);
		f->par = masked || forced;
		array_append(contains_set(tok, built) != NULL ? g->en : g->dis,
					 f);
	}
	free(tmp);

	array_sort(grps, qm_uvgrp_cmp);
	array_for_each(grps, gi, g) {
		bool first = true;

		if (array_cnt(g->en) == 0 && array_cnt(g->dis) == 0)
			continue;
		array_sort(g->en, qm_uvflag_cmp);
		array_sort(g->dis, qm_uvflag_cmp);
		printf(" %s=\"", strcmp(g->var, "USE") == 0 ? "USE" : g->var);
		array_for_each(g->en, fi, f) {
			printf("%s%s%s%s%s%s", first ? "" : " ",
				   f->par ? "(" : "", RED, f->nm, NORM,
				   f->par ? ")" : "");
			first = false;
		}
		array_for_each(g->dis, fi, f) {
			printf("%s%s%s-%s%s%s", first ? "" : " ",
				   f->par ? "(" : "", DKBLUE, f->nm, NORM,
				   f->par ? ")" : "");
			first = false;
		}
		printf("\"");
	}

	{
		char                sbuf[40];
		char               *szs = tree_pkg_meta(bpkg, Q_SIZE);
		unsigned long long  sz  = 0;

		if (szs != NULL && *szs != '\0' &&
				faccessat(tree_pkg_get_portroot_fd(bpkg),
						  tree_pkg_get_path(bpkg), R_OK, 0) != 0)
			sz = strtoull(szs, NULL, 10);
		qm_fmt_kib(sbuf, sizeof(sbuf), sz);
		printf(" %s KiB", sbuf);
	}

	array_for_each(grps, gi, g) {
		array_for_each(g->en, fi, f) {
			free(f->nm);
			free(f);
		}
		array_for_each(g->dis, fi, f) {
			free(f->nm);
			free(f);
		}
		array_free(g->en);
		array_free(g->dis);
		free(g->var);
		free(g);
	}
	array_free(grps);
	free_set(seen);
	free_set(built);
}

/* To be documented, we found a interesting thing we didn't cover
 * last times.
 * Meaning: apparently when we found this while displaying the
 * differences and comparisons like this:
 * dev-lang python 3.11.13 r1 3.11  
 * dev-lang/python-3.11.13-r1~1 < dev-lang/python-3.11.13_p1~1
 * dev-lang/python-3.11.13-r1~2 > dev-lang/python-3.11.13-r1~1 
 * Ideally when we display conflicts, we display them ONLY the ones
 * which involve latest versions.
 * Without the feature bellow, the display would have shown both
 * python3_11 versions with -r1 and _p1, which isn't correct.
 * At least not without verbose. */
static int
qm_use_reject_vercmp(const void *l, const void *r)
{
	const char *ls = *(char * const *)l;
	const char *rs = *(char * const *)r;
	char        lb[512];
	char        rb[512];
	atom_ctx   *la;
	atom_ctx   *ra;
	int         ret = 0;

	if (*ls == '=')
		ls++;
	if (*rs == '=')
		rs++;
	snprintf(lb, sizeof(lb), "%.*s",
			 (int)MIN(strcspn(ls, " \t"), sizeof(lb) - 1), ls);
	snprintf(rb, sizeof(rb), "%.*s",
			 (int)MIN(strcspn(rs, " \t"), sizeof(rb) - 1), rs);
	la = atom_explode(lb);
	ra = atom_explode(rb);
	if (la != NULL && ra != NULL) {
		switch (atom_compare(la, ra)) {
		case NEWER: ret = -1; break;
		case OLDER: ret = 1;  break;
		default:    ret = 0;  break;
		}
	}
	if (la != NULL)
		atom_implode(la);
	if (ra != NULL)
		atom_implode(ra);
	if (ret == 0)
		ret = strcmp(*(char * const *)l, *(char * const *)r);
	return ret;
}

/* We gotta print the newest rejected, and also keep
 * displaying the same versions from multiple active repos,
 * even if they're duplicates. This behavior was ok. */
static bool
qm_use_reject_veq(const char *l, const char *r)
{
	char      lb[512];
	char      rb[512];
	atom_ctx *la;
	atom_ctx *ra;
	bool      eq = false;

	if (*l == '=')
		l++;
	if (*r == '=')
		r++;
	snprintf(lb, sizeof(lb), "%.*s",
			 (int)MIN(strcspn(l, " \t"), sizeof(lb) - 1), l);
	snprintf(rb, sizeof(rb), "%.*s",
			 (int)MIN(strcspn(r, " \t"), sizeof(rb) - 1), r);
	la = atom_explode(lb);
	ra = atom_explode(rb);
	if (la != NULL && ra != NULL)
		eq = atom_compare(la, ra) == EQUAL;
	if (la != NULL)
		atom_implode(la);
	if (ra != NULL)
		atom_implode(ra);
	return eq;
}

/* check whether the reject line's instance strictly newer than the accepted one */
static bool
qm_use_reject_newer(const char *line, const char *acc)
{
	char      lb[512];
	atom_ctx *la;
	atom_ctx *aa;
	bool      newer = false;

	if (*line == '=')
		line++;
	snprintf(lb, sizeof(lb), "%.*s",
			 (int)MIN(strcspn(line, " \t"), sizeof(lb) - 1), line);
	la = atom_explode(lb);
	aa = atom_explode(acc);
	if (la != NULL && aa != NULL)
		newer = atom_compare(la, aa) == NEWER;
	if (la != NULL)
		atom_implode(la);
	if (aa != NULL)
		atom_implode(aa);
	return newer;
}

/* re-resolve the accumulated rejects.
 * this single move will cost us 50 years. */
static void
qm_use_rejects_flush(void)
{
	if (qm_use_rejects != NULL) {
		array *nv = hash_values(qm_use_rejects);

		array_deepfree(nv, set_free_cb);
		hash_free(qm_use_rejects);
		qm_use_rejects = NULL;
	}
}

static void
qm_print_use_rejects(void)
{
	array  *keys;
	size_t  n;
	char   *msg;

	/* -q drops the advisory ignore lists. this optimizes
	 * tests quote a lot. */
	if (qm_user_quiet)
		return;

	if (qm_use_rejects != NULL && hash_size(qm_use_rejects) > 0) {
		bool hdr = false;

		keys = hash_keys(qm_use_rejects);
		array_sort(keys, qm_strcmp_cb);
		array_for_each(keys, n, msg) {
			set        *d;
			array      *lines;
			size_t      ln;
			char       *line;
			const char *acc = qm_use_accepts != NULL ?
					(const char *)hash_get(qm_use_accepts, msg) : NULL;

			d = hash_get(qm_use_rejects, msg);
			lines = set_keys(d);
			array_sort(lines, qm_use_reject_vercmp);
			array_for_each(lines, ln, line) {
				if (acc != NULL && !qm_use_reject_newer(line, acc))
					break;
				if (!qm_user_verbose && ln > 0 &&
						!qm_use_reject_veq(array_get(lines, ln - 1), line))
					break;
				if (!hdr) {
					printf("\n%s!!!%s The following binary packages were "
						   "ignored due to non matching USE:\n", RED, NORM);
					hdr = true;
				}
				printf("    %s\n", line);
			}
			array_free(lines);
		}
		array_free(keys);
		if (hdr)
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

	{
		size_t pc = preserved_count(qm_preserved_get());

		if (pc > 0)
			printf("\n%s***%s %zu preserved librar%s in use; merge "
				   "@preserved-rebuild to migrate the packages still linking them\n",
				   YELLOW, NORM, pc, pc == 1 ? "y" : "ies");
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

/* parent USE context for USE-dep ([foo?]) evaluation inside
 * best_version's repo scan; set (scoped) by the resolver around its
 * calls, NULL means no USE-dep filtering (non-resolver callers) */
static set *qm_bv_parent_use = NULL;

/* dep subtree affinity: when >0, best_version prefers this binrepo
 * before priority order (deps of an explicit pkg@repo target form a
 * consistent island from that repo); set (scoped) by qm_resolve */
static ssize_t qm_repo_affinity = -1;

/* scoped: force newest-across-repos candidate selection (the conflict
 * repairer needs the real newest rebuild, not the priority-first pick,
 * which on a stale higher-priority repo is the already-installed
 * version) */
static bool qm_bv_newest = false;

/* same-slot unification. hardest portage feature there is. */
static set *qm_unify_mask = NULL;

static bool
qm_unify_masked(const depend_atom *pa)
{
	char key[512];

	if (qm_unify_mask == NULL || pa == NULL ||
			pa->CATEGORY == NULL || pa->PN == NULL || pa->PVR == NULL)
		return false;
	snprintf(key, sizeof(key), "%s/%s-%s", pa->CATEGORY, pa->PN, pa->PVR);
	return contains_set(key, qm_unify_mask) != NULL;
}

/* --keep-going candidate hiding failed packages */
static bool
qm_kg_masked(const depend_atom *pa)
{
	char key[512];

	if (qm_kg_mask == NULL || pa == NULL ||
			pa->CATEGORY == NULL || pa->PN == NULL)
		return false;
	snprintf(key, sizeof(key), "%s/%s", pa->CATEGORY, pa->PN);
	if (contains_set(key, qm_kg_mask) != NULL)
		return true;
	if (pa->SLOT == NULL)
		return false;
	snprintf(key, sizeof(key), "%s/%s:%s", pa->CATEGORY, pa->PN, pa->SLOT);
	return contains_set(key, qm_kg_mask) != NULL;
}

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

	cuse  = usedep_flags_to_set(tree_pkg_meta(cand, Q_USE));
	ciuse = usedep_flags_to_set(tree_pkg_meta(cand, Q_IUSE));
	for (ud = atom->usedeps; ud != NULL; ud = ud->next)
		if (!usedep_ok(ud, cuse, ciuse, qm_bv_parent_use)) {
			ok = false;
			break;
		}
	free_set(cuse);
	free_set(ciuse);
	return ok;
}

static array *qm_slot_members(const char *cat, const char *pn,
							  const char *slot);

/* an installed member of the candidate's slot is newer than the
 * candidate: taking this repo's best would be a downgrade */
static bool
qm_installed_slot_newer(tree_pkg_ctx *cand)
{
	depend_atom  *ca = tree_pkg_atom(cand, true);
	array        *members;
	size_t        n;
	tree_pkg_ctx *m;
	bool          newer = false;

	if (ca == NULL || ca->CATEGORY == NULL || ca->PN == NULL)
		return false;
	members = qm_slot_members(ca->CATEGORY, ca->PN, ca->SLOT);
	if (members == NULL)
		return false;
	array_for_each(members, n, m) {
		depend_atom *ma = tree_pkg_atom(m, false);

		if (ma != NULL &&
				atom_compare_flg(ma, ca,
					ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO) == NEWER) {
			newer = true;
			break;
		}
	}
	array_free(members);
	return newer;
}

static tree_pkg_ctx *
best_version(const depend_atom *atom, int mode)
{
	tree_ctx       *vdb    = qmerge_vdb_tree;
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
			qmerge_vdb_tree = vdb;
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
		bool               prefer_newest = qm_bv_newest ||
				getenv("QMERGE_PREFER_NEWEST") != NULL;
		bool               gpkg_only     = qm_sigs_mandatory();
		bool               gpkg_local    = qm_sigs_requested();
		tree_pkg_ctx      *best          = NULL;
		tree_pkg_ctx      *dgfb          = NULL;
		ssize_t            only          = -1;
		depend_atom        qa;
		const depend_atom *qq            = atom;

		/* the ::@name marker (from the pkg@binrepo CLI sigil, or a
		 * cpv::@name resolutions pin) is an explicit binhost selector:
		 * restrict the scan to that repo.Stripped for tree matching.
		 * A plain ::repo keeps the classic ebuild-repo meaning, so the
		 * two axes cannot collide once from-source builds land. 
		 * Warning note here: this is not portage specific(!!), and
		 * this is likely to be heavily changed!*/
		if (atom->REPO != NULL && atom->REPO[0] == '@' &&
				qm_nbinrepos > 0)
		{
			size_t      k;
			const char *tok = atom->REPO + 1;

			while (tok[0] == '@')
				tok++;
			for (k = 0; k < qm_nbinrepos; k++) {
				const char *rn = qm_binrepos[k].name;

				while (rn[0] == '@')
					rn++;
				if (strcmp(rn, tok) == 0) {
					only = (ssize_t)k;
					qa      = *atom;
					qa.REPO = NULL;
					qq      = &qa;
					break;
				}
			}
			if (only < 0) {
				warn("unknown binhost '%s' in selector (configured: "
					 "see binrepos.conf)", tok);
				rcnt = 0;
			}
		}

		/* scan the binrepos in priority order: within a repo pick the
		 * highest VISIBLE version (skip package.mask'd, ~testing-not-
		 * accepted, ACCEPT_LICENSE-rejected; foreign repos additionally
		 * pass the USE-match check gate).
		 * Default policy: repo priority beats version, the first repo 
		 * that can satisfy the atom wins, later repos are only consulted 
		 * when it cannot.
		 * Exceptions: a repo whose best is older than the installed
		 * slot member is skipped (downgrade guard; the priority-first
		 * pick remains the last resort when nothing serves newer);
		 * priority-0 repos form the emergency store and join only via
		 * an explicit @name selector; @local sits at the bottom of the
		 * scan unless QMERGE_LOCAL_PRIORITY raises it.
		 * QMERGE_PREFER_NEWEST=1 switches to portage-style newest-
		 * across-all-repos.
		 * An explicit ::binrepo selector scans ONLY that repo:
		 * its USE check gate demotes to a notice (user knows best)
		 * and overriding a higher-priority repo is noticed too.
		 * Quiet mode: we don't warn per skipped candidate.
		 * The merge-time check is set as loud. */
		{
			size_t order[64];
			size_t no = 0;
			size_t oi;
			size_t k;

			/* scan order: an explicit selector is that repo only; an
			 * active subtree affinity goes first, then priority order */
			if (only >= 0) {
				order[no++] = (size_t)only;
			} else {
				if (qm_repo_affinity > 0 &&
						(size_t)qm_repo_affinity < rcnt)
					order[no++] = (size_t)qm_repo_affinity;
				for (k = 0; k < qm_nbinrepos && no < 64; k++) {
					size_t w = qm_walk_order[k];

					if (w >= rcnt)
						continue;
					if (qm_repo_affinity > 0 &&
							w == (size_t)qm_repo_affinity)
						continue;
					if (qm_binrepos[w].priority == 0)
						continue;
					order[no++] = w;
				}
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

				/* the primary stays ungated (trusted): an explicitly
				 * selected or affinity-preferred foreign repo demotes a
				 * USE mismatch to a notice (the user chose this island);
				 * other foreign repos reject on mismatch */
				lenient = ri > 0 &&
						((only >= 0 && ri == (size_t)only) ||
						 (only < 0 && qm_repo_affinity > 0 &&
						  ri == (size_t)qm_repo_affinity));

				t = tree_match_atom(btree, qq,
						TREE_MATCH_SORT | TREE_MATCH_VIRTUAL |
						TREE_MATCH_ACCT);
				{
					int rmis = -1;

					/* first visible candidate settles the version.
					 * Under -N its same-version rebuilds still compete:
					 * the instance closest to the configured USE wins,
					 * newest build breaks ties (emerge picks the
					 * config-matching rebuild; plain -u keeps newest). */
					array_for_each(t, n, cand) {
						depend_atom *pa = tree_pkg_atom(cand, true);
						int          cm;

						if (rbest != NULL) {
							depend_atom ca = *pa;
							depend_atom ra = *tree_pkg_atom(rbest, true);

							ca.BUILDID = 0;
							ra.BUILDID = 0;
							if (atom_compare_flg(&ca, &ra,
									ATOM_COMP_NOSUBSLOT |
									ATOM_COMP_NOREPO) != EQUAL)
								break;
						}

						if (!qm_repo_pkg_allowed(ri, pa))
							continue;
						if ((ri == 0 ? gpkg_local : gpkg_only) &&
								!qm_path_is_gpkg(tree_pkg_get_path(cand))) {
							qm_xpak_skip_warn((ssize_t)ri);
							continue;
						}
						if (binpkg_masked(pa))
							continue;
						if (qm_unify_masked(pa))
							continue;
						if (qm_kg_masked(pa))
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
						} else if (qm_respect_use != 0 &&
								   (ri > 0 || qm_respect_use == 1) &&
								   !binpkg_use_ok(cand, pa,
									qm_nbinrepos > 0 ?
									qm_binrepos[ri].name : NULL,
									qm_respect_use == 1)) {
							continue;
						}
						if (rbest == NULL) {
							rbest = cand;
							continue;
						}
						if (!newuse)
							break;
						if (rmis < 0)
							rmis = qm_use_mismatch(rbest);
						cm = qm_use_mismatch(cand);
						if (cm < rmis) {
							rbest = cand;
							rmis  = cm;
						}
					}
				}
				array_free(t);

				if (only >= 0) {
					best = rbest;
					break;
				}
				if (rbest == NULL)
					continue;
				if (prefer_newest) {
					if (best == NULL ||
							atom_compare(tree_pkg_atom(rbest, false),
										 tree_pkg_atom(best, false)) == NEWER)
						best = rbest;
					continue;
				}
				if (dgfb == NULL)
					dgfb = rbest;
				/* downgrade guard: this repo can only downgrade the
				 * installed slot member, later repos get the chance to
				 * serve >= installed */
				if (qm_installed_slot_newer(rbest))
					continue;
				best = rbest;
				break;
			}
		}

		/* nothing can serve >= installed: fall back to the plain
		 * priority-first pick (an explicit downgrade proposal) */
		if (only < 0 && !prefer_newest && best == NULL)
			best = dgfb;

		/* explicit pick from a lower-priority repo: notice when a
		 * higher-priority repo could also satisfy the atom */
		if (only > 0 && best != NULL) {
			size_t k;

			for (k = 0; k < qm_nbinrepos; k++) {
				size_t    kw = qm_walk_order[k];
				tree_ctx *ktree;

				if (kw == (size_t)only)
					break;
				if (qm_binrepos[kw].priority == 0)
					continue;
				ktree = qm_bintree(kw);
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

					if (!qm_repo_pkg_allowed(kw, pa) ||
							((kw == 0 ? gpkg_local : gpkg_only) &&
							 !qm_path_is_gpkg(tree_pkg_get_path(cand))) ||
							binpkg_masked(pa) ||
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
							 "overriding [%s]", qm_binrepos[kw].name);
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
					/* this is unsupported(?!), so skip it.
					 * @ francoisb: why is it unsupported? */
					continue;
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

				/* full (what?) mask match */
				if ((ssize_t)maskv[i][0] == level)
					mode = child_mode =
						(ssize_t)maskv[i][level + 1] ? INCLUDE : EXCLUDE;
				else if (maskv[i][(ssize_t)maskv[i][0] + 1])
					/* partial (what?) include mask */
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

		/* we always have "something", right? */
		cnt = 1;
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
	/* allocate plus relative and include elements */
	maxdirs += 2;

	/* allocate and populate matrix.
	 * also, I think we can start documenting this fully about here. */
	masksc = iargc - 1;
	masks  = xmalloc(sizeof(char *) * (maxdirs * masksc));
	masksv = xmalloc(sizeof(char **) * (masksc));
	for (i = 1; i < iargc; i++)
	{
		masksv[i - 1] = &masks[(i - 1) * maxdirs];
		p             = iargv[i];
		cnt           = 1;

		if (*p == '-')
			p++;
		for (q = p; *p != '\0'; p++)
		{
			if (*p == '/')
			{

				if (q != p)
				{
					masks[((i - 1) * maxdirs) + cnt] = q;
					cnt++;
				}

				do
				{
					if (cnt == 1)
						p++;
					else
						*p++ = '\0';
				}
				while (*p == '/');
				if (*p == '\0')
					break;

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
	if (cnt >= _Q_PATH_MAX)
		cnt = _Q_PATH_MAX - 1;
	if (cnt > 0 && qpth[cnt - 1] == '/')
		qpth[cnt - 1] = '\0';

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
			/* TODO: compute difference */
			char *use = tree_pkg_meta(mpkg, Q_USE);
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
			/* PATH fallback */
			snprintf(buf, sizeof(buf), "q");
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
	/* align */
	{ 0,            NULL,           {0,0,0,0,0,0,0,0,0} },
	/* phase                   EAPI: 0 1 2 3 4 5 6 7 8 */
	/* table 9.3 */
	{ PKG_PRETEND,  "pkg_pretend",  {0,0,0,0,1,1,1,1,1} },
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
	/* align */
	{ 0,            NULL                  },
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
	/* let's hope latest known EAPI is closest */
		eapi = MAX_EAPI;

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
		 * separate post-phase hook (postinst_qa_check). For every other
		 * phase, an undefined func means nothing to do. */
		if (phaseidx != PKG_PREINST && phaseidx != PKG_POSTINST) {
			qprintf("--- %s\n", func);
			return;
		}
	}

	if (no_phases) {
		const char *id = strcmp(vdb_path, "vdb") == 0 &&
				qm_phase_pkg != NULL ? qm_phase_pkg : vdb_path;
		char  rp[_Q_PATH_MAX];
		FILE *rf;

		warn("skipping %s for %s (--no-phases)", func, id);
		snprintf(rp, sizeof(rp), "%svar/lib/portage", portroot);
		mkdir_p(rp, 0755);
		snprintf(rp, sizeof(rp),
				 "%svar/lib/portage/.qmerge-skipped-phases", portroot);
		if ((rf = fopen(rp, "a")) != NULL) {
			fprintf(rf, "%s %s\n", id, func);
			fclose(rf);
		}
		return;
	}

	qprintf("@@@ %s\n", func);

	if (pkg_unpack_environment(dirfd, vdb_path, T) != 0) {
		warn("cannot unpack %s/environment.bz2, skipping %s",
			 vdb_path, func);
		return;
	}

	if (qm_user_quiet)
		setenv("QMERGE_PHASE_QUIET", "1", 1);
	else
		unsetenv("QMERGE_PHASE_QUIET");

	xasprintf(&script,
		/* Provide the funcs the PMS defines as package-manager supplied
		 * (PMS chapter 12): these are exactly the ones portage's
		 * save-ebuild-env.sh strips from environment.bz2 before saving.
		 * Eclass-defined functions are preserved inside the environment
		 * and need no repo/eclass access here. The environment is
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
		/* output helpers: info to stdout, problems to stderr, like portage;
		 * -q exports QMERGE_PHASE_QUIET which mutes the info family only,
		 * ewarn/eerror always show */
		"elog() { [ -n \"${QMERGE_PHASE_QUIET}\" ] || printf ' * %%b\\n' \"$*\"; }\n"
		"einfo() { elog \"$@\"; }\n"
		"einfon() { [ -n \"${QMERGE_PHASE_QUIET}\" ] || printf ' * %%b' \"$*\"; }\n"
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
		"ebegin() { [ -n \"${QMERGE_PHASE_QUIET}\" ] || printf ' * %%b ...' \"$*\"; }\n"
		"eend() { local r=${1:-$?}; [ $# -gt 0 ] && shift; "
			"if [ ${r} -eq 0 ]; then [ -n \"${QMERGE_PHASE_QUIET}\" ] || printf ' [ ok ]\\n'; "
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
		/* install helpers: legal in pkg_preinst against ${ED} (the
		 * image about to be merged), so created entries land in
		 * CONTENTS like portage's.  baselayout uses dosym there. */
		"dodir() { local d; for d in \"$@\"; do "
			"mkdir -p \"${ED%%/}/${d#/}\" || "
				"__helpers_die \"dodir: failed to create $d\"; done; }\n"
		"keepdir() { local d f; dodir \"$@\"; for d in \"$@\"; do "
			"f=\"${ED%%/}/${d#/}/.keep_${CATEGORY}_${PN}-${SLOT%%%%/*}\"; "
			": >> \"$f\" || __helpers_die \"keepdir: failed $d\"; done; }\n"
		"dosym() { local r=; if [ \"$1\" = -r ]; then r=1; shift; fi; "
			"[ $# -eq 2 ] || { __helpers_die \"dosym: needs two "
				"arguments\"; return 1; }; "
			"local t=$1 lp=\"/${2#/}\" l=\"${ED%%/}/${2#/}\"; "
			"mkdir -p \"${l%%/*}\" || "
				"__helpers_die \"dosym: failed to create ${l%%/*}\"; "
			"if [ -n \"$r\" ]; then "
				"t=$(realpath -m --relative-to=\"${lp%%/*}\" \"$1\" "
					"2>/dev/null) || "
					"__helpers_die \"dosym: -r failed\"; fi; "
			"ln -snf \"$t\" \"$l\" || "
				"__helpers_die \"dosym: failed to create $2\"; }\n"
		"fperms() { local m=$1 f; shift; for f in \"$@\"; do "
			"chmod \"$m\" \"${ED%%/}/${f#/}\" || "
				"__helpers_die \"fperms: chmod $m $f failed\"; done; }\n"
		"fowners() { local o=$1 f; shift; for f in \"$@\"; do "
			"chown \"$o\" \"${ED%%/}/${f#/}\" || "
				"__helpers_die \"fowners: chown $o $f failed\"; done; }\n"
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
		 * (that's the "cannot change locale" spam).
		 * Default C is the only locale glibc ALWAYS has built in;
		 * C.UTF-8 needs a glibc built with it or generated locales,
		 * absent in a minimal ROOT.
		 * Override with QMERGE_PHASE_LOCALE=C.UTF-8 etc.where 
		 * that locale exists. */
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
		/* we're supporting preserved-libs now. portage equivalent.
		 * POSIX word loop, not bash pattern substitution,
		 * so the /bin/sh fallback shell can run this */
		"__qm_feat=; for __qm_f in ${FEATURES}; do "
			"[ \"${__qm_f}\" = %10$s ] || "
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
		":",
		q_self_path(),
		func,
		phase,
		portroot,
		D,
		T,
		phase_replacingvers[phaseidx].varname,
		replacing,
		debug ? "set -x;" : "",
		qm_preserve_active() ? "__qmerge_none__" : "preserve-libs");
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
			if (qm_kg_child && phaseidx == PKG_POSTINST &&
					qm_phase_pkg != NULL)
				qm_kg_announce('P', qm_phase_pkg, NULL);
		}
	}
	free(script);
}
#define pkg_run_func(...) pkg_run_func_at(AT_FDCWD, __VA_ARGS__)

/* tbd ; to be documented */
static hash_t *qm_cfg_oldmd5  = NULL;
static size_t  qm_cfg_pending = 0;
static set    *qm_cfg_dirs    = NULL;

struct qm_cm_ent {
	char *path;
	char *val;
};
static array *qm_confmem       = NULL;
static bool   qm_confmem_dirty = false;
static bool   qm_cfg_noconfmem = false;

static void
qm_confmem_load(void)
{
	char    path[_Q_PATH_MAX];
	char   *buf  = NULL;
	size_t  blen = 0;
	char   *line;
	char   *savep;

	if (qm_confmem != NULL)
		return;
	qm_confmem = array_new();

	snprintf(path, sizeof(path), "%svar/lib/portage/config", portroot);
	if (!eat_file(path, &buf, &blen)) {
		free(buf);
		return;
	}

	for (line = strtok_r(buf, "\n", &savep);
			line != NULL;
			line = strtok_r(NULL, "\n", &savep))
	{
		char             *tok;
		char             *sp2;
		char             *key = NULL;
		char              val[_Q_PATH_MAX];
		size_t            vlen = 0;
		struct qm_cm_ent *e;

		val[0] = '\0';
		for (tok = strtok_r(line, " \t", &sp2);
				tok != NULL;
				tok = strtok_r(NULL, " \t", &sp2))
		{
			if (tok[0] == '#')
				break;
			if (key == NULL) {
				key = tok;
				continue;
			}
			vlen += snprintf(val + vlen, sizeof(val) - vlen, "%s%s",
							 val[0] != '\0' ? " " : "", tok);
			if (vlen >= sizeof(val))
				break;
		}
		if (key == NULL || key[0] == '#' || val[0] == '\0')
			continue;

		e = xmalloc(sizeof(*e));
		e->path = xstrdup(key);
		e->val  = xstrdup(val);
		array_append(qm_confmem, e);
	}
	free(buf);
}

/* check whether the remembered entry's md5 (first value token) match */
static bool
qm_confmem_md5_is(const char *path, const char *md5)
{
	size_t            i;
	struct qm_cm_ent *e;
	size_t            mlen = strlen(md5);

	qm_confmem_load();
	array_for_each(qm_confmem, i, e)
		if (strcmp(e->path, path) == 0)
			return strncmp(e->val, md5, mlen) == 0 &&
					(e->val[mlen] == '\0' || e->val[mlen] == ' ');
	return false;
}

static bool
qm_confmem_has(const char *path)
{
	size_t            i;
	struct qm_cm_ent *e;

	qm_confmem_load();
	array_for_each(qm_confmem, i, e)
		if (strcmp(e->path, path) == 0)
			return true;
	return false;
}

static void
qm_confmem_set(const char *path, const char *md5)
{
	size_t            i;
	struct qm_cm_ent *e;

	qm_confmem_load();
	array_for_each(qm_confmem, i, e) {
		if (strcmp(e->path, path) != 0)
			continue;
		if (strcmp(e->val, md5) == 0)
			return;
		free(e->val);
		e->val = xstrdup(md5);
		qm_confmem_dirty = true;
		return;
	}
	e = xmalloc(sizeof(*e));
	e->path = xstrdup(path);
	e->val  = xstrdup(md5);
	array_append(qm_confmem, e);
	qm_confmem_dirty = true;
}

static void
qm_confmem_del(const char *path)
{
	size_t            i;
	struct qm_cm_ent *e;

	qm_confmem_load();
	array_for_each(qm_confmem, i, e) {
		if (strcmp(e->path, path) != 0)
			continue;
		free(e->path);
		free(e->val);
		free(e);
		array_remove(qm_confmem, i);
		qm_confmem_dirty = true;
		return;
	}
}

/* removed comments from bellow until we get this documented 
 * right here. */
static void
qm_confmem_write(void)
{
	char              path[_Q_PATH_MAX];
	char              tmp[_Q_PATH_MAX + 16];
	char             *sl;
	struct stat       st;
	bool              have;
	FILE             *fp;
	size_t            i;
	struct qm_cm_ent *e;

	if (!qm_confmem_dirty || qm_confmem == NULL || pretend)
		return;

	snprintf(path, sizeof(path), "%svar/lib/portage/config", portroot);
	snprintf(tmp, sizeof(tmp), "%s.__qmerge__", path);
	have = stat(path, &st) == 0;
	if (!have) {
		snprintf(tmp, sizeof(tmp), "%s", path);
		sl = strrchr(tmp, '/');
		if (sl != NULL) {
			*sl = '\0';
			mkdir_p(tmp, 0755);
		}
		snprintf(tmp, sizeof(tmp), "%s.__qmerge__", path);
	}

	fp = fopen(tmp, "w");
	if (fp == NULL) {
		warnp("cannot write %s", path);
		return;
	}
	bool ok = true;
	array_for_each(qm_confmem, i, e)
		if (fprintf(fp, "%s %s\n", e->path, e->val) < 0)
			ok = false;
	if (have) {
		if (fchmod(fileno(fp), st.st_mode & 07777) == 0 &&
				fchown(fileno(fp), st.st_uid, st.st_gid) != 0 &&
				errno != EPERM)
			warnp("cannot preserve ownership of %s", path);
	}
	if (fclose(fp) != 0)
		ok = false;
	if (!ok) {
		warnp("cannot write %s", path);
		unlink(tmp);
		return;
	}
	if (rename(tmp, path) != 0)
		warnp("cannot replace %s", path);
	else
		qm_confmem_dirty = false;
}

static void
qm_cfg_oldmd5_load(tree_pkg_ctx *previnst)
{
	char *cts;
	char *line;
	char *sp;

	if (qm_cfg_oldmd5 != NULL) {
		array *v = hash_values(qm_cfg_oldmd5);

		array_deepfree(v, free);
		hash_free(qm_cfg_oldmd5);
		qm_cfg_oldmd5 = NULL;
	}
	if (previnst == NULL)
		return;
	cts = tree_pkg_meta(previnst, Q_CONTENTS);
	if (cts == NULL)
		return;
	cts = xstrdup(cts);
	for (line = strtok_r(cts, "\n", &sp);
		 line != NULL;
		 line = strtok_r(NULL, "\n", &sp))
	{
		contents_entry *e = contents_parse_line(line);

		if (e != NULL && e->type == CONTENTS_OBJ &&
				e->name != NULL && e->digest != NULL)
			qm_cfg_oldmd5 = hash_add(qm_cfg_oldmd5, e->name,
									 xstrdup(e->digest), NULL);
	}
	free(cts);
}

static int
merge_backup_blocker(int dfd, const char *name, const char *cpath)
{
	char        bname[_Q_PATH_MAX];
	struct stat bst;
	int         n;

	for (n = 0; n < 10000; n++) {
		snprintf(bname, sizeof(bname), "%s.backup.%04d", name, n);
		if (fstatat(dfd, bname, &bst, AT_SYMLINK_NOFOLLOW) == 0)
			continue;
		if (errno == ENOENT)
			break;
		warnp("cannot probe a backup name for %s", cpath);
		return -1;
	}
	if (n >= 10000) {
		warn("no free backup name for %s", cpath);
		return -1;
	}
	if (renameat(dfd, name, dfd, bname)) {
		warnp("could not move %s aside", cpath);
		return -1;
	}
	warn("directory %s is blocked by a non-directory; renamed to %s",
		 cpath, bname);
	return 0;
}

/* Protection mechanism against installing packages onto the host
 * with specially crafted symlinks (that are possibly already present
 * on the new location). This should return true if the symlink at 
 * (dfd,name) whose path within the root is the cpath, escapes the root.
 * We're trying to somehoe workaround the Portage --root relocation
 * to not be hurtful even for the root user, as this operation always
 * happens only as root, never as simple user. And we must make sure
 * and warn the user that malicious symlinks might already be present
 * before we do --root '/new/location/' */
static bool
merge_symlink_escapes_root(int dfd, const char *name, const char *cpath)
{
	char        target[_Q_PATH_MAX];
	ssize_t     n;
	long        depth = 0;
	const char *p;

	n = readlinkat(dfd, name, target, sizeof(target) - 1);
	if (n < 0)
		return true;
	target[n] = '\0';

	if (target[0] == '/')
		return true;

	for (p = cpath; *p != '\0'; ) {
		const char *slash = strchr(p, '/');
		size_t      seg;

		if (slash == NULL)
			break;
		seg = (size_t)(slash - p);
		if (seg != 0 && !(seg == 1 && p[0] == '.'))
			depth++;
		p = slash + 1;
	}
	for (p = target; *p != '\0'; ) {
		const char *slash = strchr(p, '/');
		size_t      seg   = slash != NULL ? (size_t)(slash - p) : strlen(p);

		if (seg == 2 && p[0] == '.' && p[1] == '.') {
			if (--depth < 0)
				return true;
		} else if (seg != 0 && !(seg == 1 && p[0] == '.')) {
			depth++;
		}
		p = slash != NULL ? slash + 1 : p + seg;
	}
	return false;
}

/* Copy one tree (the single package) to another tree (ROOT).
 * ToDO: document fully.
 * Summarized: merge_tree_at walks one directory level and recurses
 * into subdirs, mirroring the tree onto the destination.
 * It doens't use absolute paths (so we don't get path races). */
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
	bool failed = false;

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

	i = dup(subfd_src);
	dir = fdopendir(i);
	if (!dir) {
		if (i >= 0)
			close(i);
		goto done;
	}

	cpath = *cpathp;
	clen = strlen(cpath);
	cpath[clen] = '/';
	nlen = mnlen = 0;

	while ((de = readdir(dir)) != NULL) {
		const char *name = de->d_name;

		if (filter_self_parent(de) == 0)
			continue;

		nlen = strlen(name);
		if (mnlen < nlen) {
			cpath = *cpathp = xrealloc(*cpathp, clen + 1 + nlen + 1);
			mnlen = nlen;
		}
		strcpy(cpath + clen + 1, name);

		if (fstatat(subfd_src, name, &st, AT_SYMLINK_NOFOLLOW)) {
			warnp("could not read %s", cpath);
			continue;
		}

		if (S_ISDIR(st.st_mode)) {
			struct stat dst_st;
			bool present = fstatat(subfd_dst, name, &dst_st,
					AT_SYMLINK_NOFOLLOW) == 0;
			bool keep = false;

			if (present) {
				struct stat tgt;

				if (S_ISDIR(dst_st.st_mode))
					keep = true;
				else if (S_ISLNK(dst_st.st_mode) &&
						fstatat(subfd_dst, name, &tgt, 0) == 0 &&
						S_ISDIR(tgt.st_mode)) {
					if (portroot[1] != '\0' &&
							merge_symlink_escapes_root(subfd_dst, name, cpath))
						warn("--root: relocating %s, its symlink target "
							 "escapes the root %s", cpath, portroot);
					else
						keep = true;
				}

				if (!keep && !pretend) {
					if (merge_backup_blocker(subfd_dst, name, cpath) != 0) {
						failed = true;
						continue;
					}
					if (mkdirat(subfd_dst, name, st.st_mode)) {
						warnp("could not create %s", cpath);
						failed = true;
						continue;
					}
				}
			} else if (!pretend && mkdirat(subfd_dst, name, st.st_mode) &&
					errno != EEXIST) {
				warnp("could not create %s", cpath);
				failed = true;
				continue;
			}

			if (!pretend)
				fprintf(contents, "dir %s\n", cpath);
			*objs = add_set(cpath, *objs);
			qprintf("%s---%s %s%s%s/\n", GREEN, NORM, DKBLUE, cpath, NORM);

			if (merge_tree_at(subfd_src, name,
					subfd_dst, name, contents, eprefix_len,
					objs, cpathp, cp_argc, cp_argv, cpm_argc, cpm_argv) != 0)
				failed = true;
			cpath = *cpathp;
			mnlen = 0;

			if (!pretend)
				unlinkat(subfd_dst, name, AT_REMOVEDIR);
		} else if (S_ISREG(st.st_mode)) {
			char *hash;
			const char *dname;
			char buf[_Q_PATH_MAX * 2];
			char srcmd5[136];
			struct stat ignore;
			bool prot;
			bool dest_exists;
			bool docfg;
			bool skipcfg = false;
			bool have_pending = false;

			hash = hash_file_at(subfd_src, name, HASH_MD5);
			if (!pretend)
				fprintf(contents, "obj %s %s %zu""\n",
					cpath, hash ? hash : "xxx", (size_t)st.st_mtime);

			snprintf(srcmd5, sizeof(srcmd5), "%s", hash ? hash : "");

			dest_exists = fstatat(subfd_dst, name, &ignore,
					AT_SYMLINK_NOFOLLOW) == 0;
			prot = config_protected(cpath + eprefix_len,
					cp_argc, cp_argv, cpm_argc, cpm_argv);


			docfg = false;
			if (prot && dest_exists) {
				char *dmd5   = hash_file_at(subfd_dst, name, HASH_MD5);
				bool  active = true;

				/* unmodified relative to the replaced instance: not
				 * really protected (config-protect-if-modified) */
				if (dmd5 != NULL && qm_cfg_oldmd5 != NULL &&
						contains_set("config-protect-if-modified",
									 features)) {
					char *omd5 = hash_get(qm_cfg_oldmd5, cpath);

					if (omd5 != NULL && strcmp(omd5, dmd5) == 0)
						active = false;
				}
				if (active) {
					docfg = true;
					if (dmd5 != NULL && srcmd5[0] != '\0') {
						if (strcmp(dmd5, srcmd5) == 0) {
							docfg = false;
						} else if (qm_confmem_md5_is(cpath, srcmd5)) {
							/* the identical update was offered before:
							 * skip it entirely (portage confmem);
							 * downgrades and NOCONFMEM ignore the
							 * memory and offer again */
							docfg   = qm_cfg_noconfmem;
							skipcfg = !qm_cfg_noconfmem;
						}
						if (!pretend) {
							if (!skipcfg)
								qm_confmem_set(cpath, srcmd5);
							else if (qm_confmem_md5_is(cpath, dmd5))
								qm_confmem_del(cpath);
						}
					}
				}
			} else if (prot && !dest_exists) {
				/* admin deleted a file the replaced instance owned:
				 * we still offer the update as ._cfg so the deletion is
				 * respected (portage bug #523684) */
				if (qm_cfg_oldmd5 != NULL &&
						hash_get(qm_cfg_oldmd5, cpath) != NULL)
					docfg = true;
			}

			if (skipcfg) {
				/* confmem rejected this update */
				dname = name;
				qprintf("%s---%s %s\n", GREEN, NORM, cpath);
			} else if (docfg) {
				char *num;
				char  lastcfg[_Q_PATH_MAX * 2];
				bool  found_prev = false;

				dname = buf;
				snprintf(buf, sizeof(buf), "._cfg####_%s", name);
				num = buf + 5;
				for (i = 0; i < 10000; ++i) {
					sprintf(num, "%04i", i);
					num[4] = '_';
					if (fstatat(subfd_dst, dname, &ignore, AT_SYMLINK_NOFOLLOW))
						break;
					snprintf(lastcfg, sizeof(lastcfg), "%.4095s", dname);
					found_prev = true;
				}
				if (found_prev) {
					char *pmd5 = hash_file_at(subfd_dst, lastcfg,
											  HASH_MD5);

					if (pmd5 != NULL && srcmd5[0] != '\0' &&
							strcmp(pmd5, srcmd5) == 0)
						have_pending = true;
				}
				qm_cfg_pending++;
				{
					char  dbuf[_Q_PATH_MAX];
					char *sl;

					snprintf(dbuf, sizeof(dbuf), "%s", cpath);
					sl = strrchr(dbuf, '/');
					if (sl != NULL && sl != dbuf)
						*sl = '\0';
					if (qm_cfg_dirs == NULL)
						qm_cfg_dirs = create_set();
					add_set_unique(dbuf, qm_cfg_dirs, NULL);
				}
				if (have_pending)
					qprintf("%s---%s %s (pending update already queued)\n",
							GREEN, NORM, cpath);
				else
					qprintf("%s>>>%s %s (%s)\n", GREEN, NORM, cpath, dname);
			} else {
				dname = name;
				qprintf("%s>>>%s %s\n", GREEN, NORM, cpath);
			}
			*objs = add_set(cpath, *objs);

			if (pretend)
				continue;

			if (!skipcfg && !have_pending &&
					move_file(subfd_src, name, subfd_dst, dname, &st) != 0) {
				warnp("failed to move file from %s", cpath);
				failed = true;
			}
		} else if (S_ISLNK(st.st_mode)) {
			/* Migrate a symlink.
			 * because we have nothing else to say here, right? */
			char sym[_Q_PATH_MAX];
			ssize_t symlen = readlinkat(subfd_src, name, sym,
										sizeof(sym) - 1);

			if (symlen < 0) {
				warnp("could not read link %s", cpath);
				failed = true;
				continue;
			}
			sym[symlen] = '\0';

			/* syntax: sym src -> dst mtime */
			if (!pretend)
				fprintf(contents, "sym %s -> %s %zu\n",
						cpath, sym, (size_t)st.st_mtime);
			qprintf("%s>>>%s %s%s -> %s%s\n", GREEN, NORM,
					CYAN, cpath, sym, NORM);
			*objs = add_set(cpath, *objs);

			if (pretend)
				continue;

			if (symlinkat(sym, subfd_dst, name)) {
				if (errno != EEXIST ||
				    unlinkat(subfd_dst, name, 0) ||
				    symlinkat(sym, subfd_dst, name)) {
					warnp("could not create link %s to %s", cpath, sym);
					failed = true;
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
			failed = true;
			continue;
		}
	}

	closedir(dir);
	ret = failed ? -1 : 0;

 done:
	close(subfd_src);
	close(subfd_dst);

	return ret;
}

struct qm_xpak_extract_ctx {
	int  fd;
	bool error;
};

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
	struct qm_xpak_extract_ctx *xc = ctx;
	(void)pathname_len;

	int fd = openat(xc->fd, pathname,
			O_WRONLY | O_CLOEXEC | O_CREAT | O_TRUNC, 0644);
	if (fd < 0) {
		xc->error = true;
		return;
	}
	out = fdopen(fd, "w");
	if (!out) {
		close(fd);
		xc->error = true;
		return;
	}

	if (fwrite(data + data_offset, 1, data_len, out) != (size_t)data_len)
		xc->error = true;
	if (fclose(out) != 0)
		xc->error = true;
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

	if (n > 0) {
		n = fread(s->buf, 1, n, s->f);
		if (n == 0 && ferror(s->f)) {
			archive_set_error(a, EIO, "read error on bounded tar stream");
			return ARCHIVE_FATAL;
		}
	}
	s->left -= n;
	*bufp = s->buf;
	return (la_ssize_t)n;
}

/* ---- resolver S1: atom satisfaction incl. USE-dep constraints ---- */

/* check whether a candidate package cand satisfy dependency atom dep.
 * category/PN/version/operator/slot/subslot via the standard
 * matcher (subslot now compares by effective value); a ::@binrepo
 * selector is NOT an ebuild-repo constraint, ignore REPO for it
 * (best_version already restricted the scan) */
static bool
atom_satisfied_by(atom_ctx *dep, tree_pkg_ctx *cand, set *parent_use)
{
	atom_ctx *ca = tree_pkg_atom(cand, dep->SLOT != NULL);

	if (atom_compare_flg(ca, dep,
			dep->REPO != NULL && dep->REPO[0] == '@' ?
			ATOM_COMP_DEFAULT | ATOM_COMP_NOREPO : ATOM_COMP_DEFAULT)
			!= EQUAL)
		return false;

	if (dep->usedeps != NULL) {
		set               *cuse  = usedep_flags_to_set(tree_pkg_meta(cand, Q_USE));
		set               *ciuse = usedep_flags_to_set(tree_pkg_meta(cand, Q_IUSE));
		const atom_usedep *ud;
		bool               ok    = true;

		for (ud = dep->usedeps; ud != NULL; ud = ud->next)
			if (!usedep_ok(ud, cuse, ciuse, parent_use)) {
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

/* ---- resolver S2: || (any-of) choice via dep_zapdeps ranking ---- */

enum {
	/* every atom satisfied by an installed pkg */
	QM_RANK_INSTALLED = 0,
	/* every atom satisfiable via a binpkg      */
	QM_RANK_AVAILABLE = 1,
	/* not fully satisfiable                    */
	QM_RANK_OTHER     = 2,
};

/* classify one || branch. fully satisfied by installed packages ||
 * || available via binpkgs || unsatisfiable.
 * New-style virtual category atoms clone portage's semantics */
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
		qm_bv_parent_use = parent_use;
		bin  = best_version(a, BV_BINPKG);
		qm_bv_parent_use = NULL;
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

/* choose one branch of an || group. Cloning portage dep_zapdeps: the
 * best-ranked branch wins, ties broken by source order (first).
 * An already-installed-satisfied branch (e.g. the installed alternative of
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
			/* cannot do better; first installed wins */
			if (r == QM_RANK_INSTALLED)
				break;
		}
	}
	return best;
}

/* ---- resolver S3: transitive resolve pass producing the merge list ---- */

struct qm_plan {
	/* owned cpv (CAT/PF) strings, dependency order */
	array *merge;
	/* cpv already appended */
	set   *in_merge;
	/* provider cpv whose deps the descent covered */
	set   *examined;
};

static hash_t *qm_plan_inst = NULL;

static void
qm_plan_inst_free(void)
{
	array  *k;
	size_t  i;
	char   *key;

	if (qm_plan_inst == NULL)
		return;
	k = hash_keys(qm_plan_inst);
	if (k != NULL) {
		array_for_each(k, i, key)
			free(hash_get(qm_plan_inst, key));
		array_free(k);
	}
	hash_free(qm_plan_inst);
	qm_plan_inst = NULL;
}

/* every resolved dep edge lands in qm_demands as cpslot -> "revdep\1atom" */
static hash_t *qm_demands = NULL;
static char    qm_cur_revdep[560] = "";
static int     qm_unsat_cnt = 0;
static int     qm_unify_round = 0;
static set    *qm_unsat_noted = NULL;
static bool    qm_internal_pull = false;

static void
qm_demands_free(void)
{
	array  *k;
	size_t  i;
	char   *key;

	if (qm_demands == NULL)
		return;
	k = hash_keys(qm_demands);
	if (k != NULL) {
		array_for_each(k, i, key)
			array_deepfree((array *)hash_get(qm_demands, key), free);
		array_free(k);
	}
	hash_free(qm_demands);
	qm_demands = NULL;
}

static void
qm_demand_record(const char *cpslot, const char *atomstr)
{
	array *d;
	char  *rec;

	if (qm_demands == NULL)
		return;
	d = hash_get(qm_demands, cpslot);
	if (d == NULL) {
		d = array_new();
		qm_demands = hash_add(qm_demands, cpslot, d, NULL);
	}
	xasprintf(&rec, "%s\1%s",
			  qm_cur_revdep[0] != '\0' ?
					qm_cur_revdep : "(your majesty)",
			  atomstr);
	array_append(d, rec);
}

/* count every unsatisfied dep, but on re-resolve rounds warn only the
 * first time per atom. */
static bool
qm_unsat_note(const char *atomstr)
{
	qm_unsat_cnt++;
	if (qm_unsat_noted == NULL)
		qm_unsat_noted = create_set();
	if (contains_set(atomstr, qm_unsat_noted) != NULL)
		return qm_unify_round == 0;
	add_set(atomstr, qm_unsat_noted);
	return true;
}

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

/* check whether the binpkg is strictly newer (version-wise) than the installed one.
 * used by -D (deep) to decide whether to upgrade an already-satisfied dep.
 * Ignores subslot/ repo, same as the [U] status test in qm_slot_status. */
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

/* -F forces newest binpkgs to match the atom across repos with no soft filters
 * Somewhat clone the qm_repair_pick repo-scan.*/
static tree_pkg_ctx *
qm_force_pick(atom_ctx *atom)
{
	size_t        rcnt = qm_bintree_cnt();
	size_t        ri;
	tree_pkg_ctx *best = NULL;

	for (ri = 0; ri < rcnt; ri++) {
		tree_ctx     *bt = qm_bintree(ri);
		array        *t;
		size_t        n;
		tree_pkg_ctx *cand;

		if (bt == NULL)
			continue;
		t = tree_match_atom(bt, atom,
				TREE_MATCH_SORT | TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);
		array_for_each(t, n, cand) {
			if (best == NULL ||
					atom_compare(tree_pkg_atom(cand, true),
								 tree_pkg_atom(best, true)) == NEWER)
				best = cand;
			/* highest-first within repo: first is this repo's best.
			 * mimic the regular distros style without slots */
			break;
		}
		array_free(t);
	}
	return best;
}

/* needs documenting*/
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

	if (qm_atom_excluded(atom)) {
		char key[520];

		snprintf(key, sizeof(key), "%s/%s",
				 atom->CATEGORY ? : "", atom->PN ? : "");
		if (qm_exclude_noted == NULL)
			qm_exclude_noted = create_set();
		if (contains_set(key, qm_exclude_noted) == NULL) {
			add_set(key, qm_exclude_noted);
			if (!qm_user_quiet)
				printf("%s>>>%s excluding %s \n",
					   YELLOW, NORM, key);
		}
		return;
	}

	inst = best_version(atom, BV_INSTALLED);
	qm_bv_parent_use = parent_use;
	if (level == 0 && qm_forcing_target) {
		bin = qm_force_pick(atom);
		if (bin != NULL) {
			atom_ctx *fa = tree_pkg_atom(bin, false);
			char      fcpv[512];

			snprintf(fcpv, sizeof(fcpv), "%s/%s",
					 fa->CATEGORY ? : "", fa->PF ? : "");
			if (qm_force_targets == NULL)
				qm_force_targets = create_set();
			add_set(fcpv, qm_force_targets);
		}
	} else {
		bin = best_version(atom, BV_BINPKG);
	}
	qm_bv_parent_use = NULL;

	if (level == 0) {
		/* an explicitly requested atom is always (re)installed from the
		 * best available binpkg, like `emerge -K <pkg>`, it shows as
		 * [R] when the same version is installed, [U] when newer.
		 * Only dependencies (level > 0) are skipped when already satisfied. */
		if (bin != NULL && atom_satisfied_by(atom, bin, parent_use)) {
			provider = bin;
			pull     = true;
			/* -u: emerge --update semantics, a target whose installed
			 * copy is current is skipped; a newer binpkg, a config
			 * USE change (-N, installed vs config) or a binhost
			 * rebuild (rebuilt-binaries) still pulls
			 * Drift and rebuilt never pull a bin OLDER than installed 
			 * (all newer instances USE-rejected).
			 * hold the installed copy instead. */
			if (update_only && inst != NULL &&
					atom_satisfied_by(atom, inst, parent_use) &&
					!qm_bin_newer(bin, inst) &&
					!(newuse && qm_use_changed(bin, inst) &&
					  !qm_bin_newer(inst, bin)) &&
					!(rebuilt_bins && qm_rebuilt_newer(bin, inst) &&
					  !qm_bin_newer(inst, bin))) {
				provider = inst;
				pull     = false;
			}
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

			if (qm_internal_pull)
				warn("cannot satisfy %s%s%s", atom_to_string(atom), h, mh);
			else if (qm_unsat_note(atom_to_string(atom)))
				warn("cannot satisfy %s%s%s", atom_to_string(atom), h, mh);
			return;
		}
	} else if (deep && bin != NULL && atom_satisfied_by(atom, bin, parent_use) &&
			   (qm_bin_newer(bin, inst) ||
				(newuse && inst != NULL && qm_use_changed(bin, inst) &&
				 !qm_bin_newer(inst, bin)) ||
				(rebuilt_bins && inst != NULL &&
				 qm_rebuilt_newer(bin, inst) &&
				 !qm_bin_newer(inst, bin)))) {
		/* -D: proactively upgrade a satisfied dep to a strictly newer binpkg
		 * (never a downgrade), giving `emerge -uD`-style deep updates.
		 * With -N an installed copy whose built USE fell out of line
		 * with the config (e.g. new PYTHON_TARGETS) also counts, like
		 * emerge --newuse. */
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
		/* new-style virtual, zero-cost, no provider */
		return;
	} else {
		const char *h  = qm_excl_hint(atom);
		const char *mh = qm_move_fail_hint(atom);

		if (qm_unsat_note(atom_to_string(atom)))
			warn("cannot satisfy dependency %s%s%s",
				 atom_to_string(atom), h, mh);
		return;
	}

	/* anti-downgrade order: a dependency must never pull a provider OLDER than what's
	 * already installed in that slot.
	 * A stale := revdep (built against foo:0/OLD) otherwise drags 
	 * foo *down* to OLD to satisfy its subslot bind.
	 * Keep the installed provider instead and let the sweep flag the stale
	 * revdep for rebuild.
	 * (level 0 is the explicit target, leave it be.) */
	if (pull && level > 0 && provider == bin && bin != NULL) {
		tree_pkg_ctx *cur;

		ratom = atom;
		if (atom->SUBSLOT != NULL && atom->SUBSLOT != atom->SLOT) {
			/* shallow copy shares all pointers */
			neut         = *atom;
			/* look up the installed slot occupant */
			neut.SUBSLOT = neut.SLOT;
			ratom        = &neut;
		}
		/* invalidates inst (used) */
		cur = best_version(ratom, BV_INSTALLED);
		if (cur != NULL && qm_bin_newer(cur, bin)) {
			/* installed slot version is newer -> keep it */
			provider = cur;
			pull     = false;
		}
	}

	/* B1: tree_pkg_ctx from best_version() is backed by a cached tree
	 * and is invalidated by further best_version() calls; copy out
	 * everything we need BEFORE recursing (which makes many such
	 * calls), and carry the cpv, not the ctx, in the merge list */
	patom = tree_pkg_atom(provider, false);
	snprintf(cpv, sizeof(cpv), "%s/%s",
			 patom->CATEGORY != NULL ? patom->CATEGORY : "",
			 patom->PF != NULL ? patom->PF : "");
	{
		ssize_t prov_repo = qm_repoidx_of_pkg(provider);

		/* pin the serving binrepo into the merge-list entry (cpv::@binrepo)
		 * so every downstream =cpv re-resolution (display, prefetch,
		 * fetch, conflict scan) lands on the SAME repo, without
		 * this, a version present on several binhosts re-resolves by
		 * priority and an explicit selection would silently merge the
		 * wrong build */
		if (pull && qm_nbinrepos > 1 && prov_repo >= 0) {
			size_t cl = strlen(cpv);

			if (cl < sizeof(cpv) - 4)
				snprintf(cpv + cl, sizeof(cpv) - cl, "::@%s",
						 qm_binrepos[prov_repo].name);
		}

		/* pull-time notices: only packages REALLY entering the resolution
		 * from a foreign repo get lines, a dep merely evaluated but
		 * satisfied by the installed system stays silent */
		if (pull && prov_repo > 0 &&
				((atom->REPO != NULL && atom->REPO[0] == '@') ||
				 (level > 0 && qm_repo_affinity == prov_repo)))
		{
			char        key[512];
			char        msg[512];
			char        why[160];
			const char *how = atom->REPO != NULL && atom->REPO[0] == '@'
					? "explicitly requested" : "@repo subtree affinity";

			snprintf(key, sizeof(key), "=%s [%s]",
					 atom_to_string(tree_pkg_atom(provider, true)),
					 qm_binrepos[prov_repo].name);

			if (level > 0 && qm_repo_affinity == prov_repo) {
				snprintf(msg, sizeof(msg),
						 "pulled as dependency by @%s subtree affinity",
						 qm_binrepos[prov_repo].name);
				qm_notice(key, msg);
			}
			if (!binpkg_use_ok_r(provider, tree_pkg_atom(provider, true),
								 qm_binrepos[prov_repo].name,
								 qm_respect_use == 1, why, sizeof(why)))
			{
				snprintf(msg, sizeof(msg),
						 "USE mismatch: %s -- proceeding (%s)", why, how);
				qm_notice(key, msg);
			}
		}

		/* explicit @repo target: its whole dep subtree prefers that
		 * repo (consistent island); kept in check & restored after the scan */
		if (atom->REPO != NULL && atom->REPO[0] == '@' && prov_repo > 0)
			aff_new = prov_repo;
	}
	if (pull && qm_plan_inst != NULL &&
			hash_get(qm_plan_inst, cpv) == NULL) {
		char *ipath = tree_pkg_meta(provider, Q_PATH);

		if (ipath != NULL && ipath[0] != '\0')
			hash_add(qm_plan_inst, cpv, xstrdup(ipath), NULL);
	}
	if (qm_demands != NULL && !(qm_internal_pull && level == 0)) {
		atom_ctx *sa = tree_pkg_atom(provider, true);
		char      dslot[512];

		snprintf(dslot, sizeof(dslot), "%s/%s:%s",
				 sa->CATEGORY ? : "", sa->PN ? : "", sa->SLOT ? : "");
		qm_demand_record(dslot, atom_to_string(atom));
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
	 * the requested atom (level 0).
	 * With -D, descend into everything including already-satisfied installed deps.
	 * So the whole tree is checked for updates, matching `emerge --deep`.
	 * ( Yes, we know this is slightly dangerous, but it's the closest to optimized
	 * solution we found. ) */
	if ((pull || level == 0 || deep) && follow_rdepends) {
		char    *deps[2];
		int      di;
		ssize_t  aff_save = qm_repo_affinity;
		char     csave[sizeof(qm_cur_revdep)];

		memcpy(csave, qm_cur_revdep, sizeof(csave));
		snprintf(qm_cur_revdep, sizeof(qm_cur_revdep), "%s", cpv);

		/* deps evaluated under the PROVIDER's built USE (an alien
		 * repo's package resolves its subtree with the flags it was
		 * really built with); an explicit @repo target additionally
		 * turns on subtree affinity for the recursion below */
		if (aff_new > 0)
			qm_repo_affinity = aff_new;

		use = usedep_flags_to_set(usestr);
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

		qm_repo_affinity = aff_save;
		memcpy(qm_cur_revdep, csave, sizeof(qm_cur_revdep));
	}

	/* post-order: append after deps so merge order is deps-first */
	if (pull)
		qm_plan_add(plan, cpv);

	free(usestr);
	free(rdep);
	free(pdep);
}

/* we need a better explanation for what this serves
 * because everyone knows what this is.  */
static int
qm_strcmp_cb(const void *l, const void *r)
{
	return strcmp(*(char * const *)l, *(char * const *)r);
}

/* portage cpv_expand disambiguation (lib/portage/dbapi/cpv_expand.py):
 * qualify a bare package name: collect every category that carries it,
 * across PKGDIR, the VDB and every configured binhost store.
 * Portage clone (dep_expand AmbiguousPackageName): one category =>
 * qualified; more than one => ambiguous, the caller must
 * refuse and list the candidates.
 * Returns an owned "category" string, or NULL if unresolved (0
 * matches) / ambiguous.  *ambiguous set accordingly; when cands is
 * non-NULL it receives the owned candidate-category set. */
static char *
qm_pick_category(const char *pn, bool *ambiguous, set **cands)
{
	atom_ctx     *bare;
	set          *cats;
	array        *matches;
	size_t        i;
	tree_pkg_ctx *pkg;
	char         *chosen = NULL;
	int           tt;
	size_t        rcnt;
	size_t        ri;

	*ambiguous = false;
	if (cands != NULL)
		*cands = NULL;
	bare = atom_explode(pn);
	if (bare == NULL)
		return NULL;

	cats = create_set();
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

	rcnt = qm_bintree_cnt();
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
		matches = tree_match_atom(bt, bare,
				TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);
		array_for_each(matches, i, pkg) {
			atom_ctx *pa = tree_pkg_atom(pkg, false);

			if (pa->CATEGORY != NULL)
				add_set_unique(pa->CATEGORY, cats, NULL);
		}
		array_free(matches);
	}
	atom_implode(bare);

	if (cnt_set(cats) == 1) {
		array *catlist = set_keys(cats);

		if (array_cnt(catlist) == 1)
			chosen = xstrdup(array_get(catlist, 0));
		array_free(catlist);
	} else if (cnt_set(cats) > 1) {
		*ambiguous = true;
	}

	if (cands != NULL)
		*cands = cats;
	else
		free_set(cats);
	return chosen;
}

/* Return the installed VDB packages in cat/pn that occupy the same SLOT
 * as `slot` (NULL/empty treated as "0", per PMS).
 * Uses a bare cat/pn match plus an explicit SLOT filter rather than a slot-qualified atom,
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
	tree_ctx     *vdb  = qmerge_vdb_tree;
	const char   *want = (slot != NULL && slot[0] != '\0') ? slot : "0";
	size_t        n;
	tree_pkg_ctx *m;

	if (cat == NULL || pn == NULL)
		return ret;
	if (vdb == NULL) {
		vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);
		qmerge_vdb_tree = vdb;
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
			atom_ctx   *ma = tree_pkg_atom(m, true);
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
 * NS ("new slot") if it lives only in a DIFFERENT slot.
 * Mirrors portage's slot-based view so the merge list matches emerge.
 * fromver (if non-NULL) gets the replaced version, valid 
 * while the vdb tree stays open, else NULL. */
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
 * news-<repoid>.unread. Read-only: qmerge does not sync, so it never
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

/* We're implemenitng a NSSfree lookup in which we parse ROOT's etc/group
 * and etc/passwd. The model method is from Alpine's APK. A static qmerge
 * apparently segfaults when fetching -f atoms under systemd if we 
 * use getgrnam under glibc.*/
static gid_t
qm_group_gid(const char *name)
{
	char          path[_Q_PATH_MAX];
	FILE         *f;
	struct group *gr;
	gid_t         gid = (gid_t)-1;

	snprintf(path, sizeof(path), "%setc/group", portroot);
	if ((f = fopen(path, "re")) == NULL)
		return gid;
	while ((gr = fgetgrent(f)) != NULL)
		if (strcmp(gr->gr_name, name) == 0) {
			gid = gr->gr_gid;
			break;
		}
	fclose(f);
	return gid;
}

static uid_t
qm_passwd_uid(const char *name, gid_t *gidp)
{
	char           path[_Q_PATH_MAX];
	FILE          *f;
	struct passwd *pw;
	uid_t          uid = (uid_t)-1;

	snprintf(path, sizeof(path), "%setc/passwd", portroot);
	if ((f = fopen(path, "re")) == NULL)
		return uid;
	while ((pw = fgetpwent(f)) != NULL)
		if (strcmp(pw->pw_name, name) == 0) {
			uid = pw->pw_uid;
			if (gidp != NULL)
				*gidp = pw->pw_gid;
			break;
		}
	fclose(f);
	return uid;
}

/* portage-parity merge history: qlop-parseable records appended to
 * EMERGE_LOG_DIR/emerge.log (same file, format and perms as portage),
 * so qlop -muv answers "what happened on this box" for qmerge-driven
 * systems too.
 * Lazily opened on first record; silent on failure.
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
			gid_t gid = qm_group_gid("portage");

			/* perms stay root-only */
			if (gid != (gid_t)-1 && fchown(fd, 0, gid) != 0) {
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

static tree_pkg_ctx *qm_plan_pick(const char *cpvp, atom_ctx *ca);

/* Download the whole merge list into PKGDIR up front with a bounded pool of
 * `jobs` forked workers, so the network isn't twiddling its thumbs one
 * package at a time. Each worker only pulls its own gpkg (distinct file,
 * no VDB, no shared state), a botched download just gets refetched by
 * the serial pkg_fetch afterwards.
 * Workers open their own trees so they never trample the parent's tree
 * fds across the fork. */
static void
qm_prefetch(array *merge, int jobs)
{
	size_t i;
	char  *cpvp;
	int    running = 0;

	if (jobs < 2 || array_cnt(merge) < 2)
		/* nothing to parallelize */
		return;

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

		/* emerge-style per-package progress so a big merge list does not look
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
			 * was closed at parse time.Drop the vdb tree, the download
			 * path never needs it. */
			atom_ctx     *ca;
			tree_pkg_ctx *bp;
			char          ex[520];

			qmerge_vdb_tree    = NULL;
			snprintf(ex, sizeof(ex), "=%s", cpvp);
			ca = atom_explode(ex);
			if (ca != NULL) {
				bp = qm_plan_pick(cpvp, ca);
				if (bp != NULL)
					pkg_download(bp);
			}
			_exit(0);
		}
		if (pid > 0)
			running++;
	}

	while (running > 0) {
		if (waitpid(-1, NULL, 0) > 0)
			running--;
		else
			break;
	}

	unsetenv("QMERGE_REFETCH");

	qm_dl_n = qm_dl_total = 0;
}

/* a cat/pn:slot whose subslot the resolution changes, and what it changes to */
struct qm_edge {
	/* "cat/pf" of the pkg holding the dep (for messages) */
	char *revdep;
	/* the atom, re-exploded when resolving (positive form) */
	char *atomstr;
	/* revdep USE flags, for parent-conditional use-deps */
	char *cusestr;
	/* 1 = ! / !! blocker edge, 0 = slot-satisfaction edge */
	int   is_blocker;
	/* blocker only: 1 = !! (hard), 0 = ! (soft) */
	int   hard;
	/* 1 = slotless version edge (1c), madtched across slots */
	int   slotless;
	/* "cat/pn:slot" of the revdep, Layer 2 upgrade target */
	char *revdep_cpslot;
};

struct qm_scctx {
	/* "cat/pn:slot" being (re)installed by the resolution */
	set   *planned;
	/* "cat/pn" the resolution touches (any slot), for 1c */
	set   *planned_cpn;
	/* struct qm_edge *, revdep edges to check */
	array *edges;
	/* nullable: Layer 2 collects wayard revdeps to upgrade */
	set   *fixable;
	/* nullable: revdep -> set of broken atomstr */
	hash_t *fix_edges;
	int    conflicts;
	int    printed;
};

/* a surviving/planned pkg needs an atom the end-state no longer satisfies and
 * we can't install it from a binpkg, shared reporter, caps the noise */
static void
qm_report_conflict(struct qm_scctx *sc, const char *revdep,
				   const char *atomstr, const char *revdep_cpslot)
{
	if (qm_tolerated != NULL && revdep_cpslot != NULL &&
			atomstr != NULL) {
		char tk[1024];

		snprintf(tk, sizeof(tk), "%s\1%s", revdep_cpslot, atomstr);
		if (contains_set(tk, qm_tolerated) != NULL) {
			if (sc->fixable == NULL)
				warn("%s: pin %s left unsatisfied (no acceptable "
					 "rebuilt binpkg on any binhost); continuing. ",
					 revdep, atomstr);
			return;
		}
	}
	sc->conflicts++;
	/* Layer 2: a slot/slotless strand is fixable by upgrading the dangling package */
	if (sc->fixable != NULL) {
		if (revdep_cpslot != NULL)
			add_set(revdep_cpslot, sc->fixable);
		if (sc->fix_edges != NULL && atomstr != NULL) {
			const char *ck = revdep_cpslot != NULL ?
					revdep_cpslot : revdep;
			set        *es = hash_get(sc->fix_edges, ck);

			if (es == NULL) {
				es = create_set();
				hash_add(sc->fix_edges, ck, es, NULL);
			}
			add_set_unique(atomstr, es, NULL);
		}
		return;
	}
	if (sc->printed < 12) {
		warn("dep conflict: %s needs %s, but the plan installs a version "
			 "that no longer satisfies it -- can't install it from a binpkg",
			 revdep, atomstr);
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

/* emerge style blocker rendering. */
static array *qm_blk_lines   = NULL;
static set   *qm_blk_seen    = NULL;
static bool   qm_blk_collect = false;

static void
qm_blk_key(const char *atomstr, const char *who, char *key, size_t keylen)
{
	char  whob[520];
	char *m;

	snprintf(whob, sizeof(whob), "%s", who);
	m = strstr(whob, "::@");
	if (m != NULL)
		*m = '\0';
	snprintf(key, keylen, "%s\1%s", atomstr, whob);
}

static void
qm_blk_reset(void)
{
	if (qm_blk_lines != NULL) {
		array_deepfree(qm_blk_lines, free);
		qm_blk_lines = NULL;
	}
	if (qm_blk_seen != NULL) {
		free_set(qm_blk_seen);
		qm_blk_seen = NULL;
	}
}

static void
qm_blk_record(const char *atomstr, const char *who, int hard)
{
	char  key[1100];
	char *rec;

	qm_blk_key(atomstr, who, key, sizeof(key));
	if (qm_blk_seen == NULL)
		qm_blk_seen = create_set();
	if (contains_set(key, qm_blk_seen) != NULL)
		return;
	add_set(key, qm_blk_seen);
	if (qm_blk_lines == NULL)
		qm_blk_lines = array_new();
	xasprintf(&rec, "%s\1%c", key, hard ? 'H' : 'S');
	array_append(qm_blk_lines, rec);
}

/* print the collected lines once, freeing them (the seen set stays to
 * silence the loud sweep); true = something was printed */
static bool
qm_print_blocks(void)
{
	size_t i;
	char  *rec;
	bool   any = false;

	if (qm_blk_lines == NULL)
		return false;
	array_for_each(qm_blk_lines, i, rec) {
		char *who  = strchr(rec, '\1');
		char *hard;

		if (who == NULL)
			continue;
		*who++ = '\0';
		hard = strchr(who, '\1');
		if (hard == NULL)
			continue;
		*hard++ = '\0';
		printf("%s[blocks B      ] %s (\"%s\" is %s blocking %s)%s\n",
			   RED, rec, rec, *hard == 'H' ? "hard" : "soft", who, NORM);
		any = true;
	}
	array_deepfree(qm_blk_lines, free);
	qm_blk_lines = NULL;
	return any;
}

/* a blocker (! / !!) is violated in the end-state: `who` blocks `blocked`.
 * default is to refuse rather than auto-unmerge something the user didn't
 * ask to drop. QMERGE_BLOCKERS opts into portage-style soft-block
 * resolution: when the merge list (a fresh/planned pkg) SOFT-blocks an already
 * INSTALLED pkg, collect that installed pkg for a safe unmerge before the
 * merge, and treat it as resolved (not a conflict). Hard blockers (!!),
 * and blocks against not-yet-installed merge-list members, still refuse. */
static void
qm_report_blocker(struct qm_scctx *sc, const char *who, const char *atomstr,
				  const char *blocked, int hard)
{
	if (qmerge_blockers && !hard &&
			(sc->fixable == NULL || qm_blk_collect) &&
			qm_cpv_installed(blocked)) {
		if (qm_soft_unmerge == NULL)
			qm_soft_unmerge = create_set();
		add_set(blocked, qm_soft_unmerge);
		return;
	}
	sc->conflicts++;
	if (sc->fixable != NULL) {
		if (qm_blk_collect)
			qm_blk_record(atomstr, who, hard);
		return;
	}
	if (qm_blk_seen != NULL) {
		char key[1100];

		qm_blk_key(atomstr, who, key, sizeof(key));
		if (contains_set(key, qm_blk_seen) != NULL)
			return;
	}
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

/* does the resolution install a package (other than exclude_cpv) that the positive
 * atom `pos` matches? fills `hit` with the offending cpv.
* best_version here is safe, callers run it outside the vdb enumeration. */

/* falling back to best_version for entries without a record
 * record (installed-provider cpvs, stores without PATH metadata). */
static tree_pkg_ctx *
qm_plan_pick(const char *cpvp, atom_ctx *ca)
{
	const char *want = qm_plan_inst != NULL ?
			(const char *)hash_get(qm_plan_inst, cpvp) : NULL;

	if (want != NULL) {
		size_t    rcnt = qm_bintree_cnt();
		size_t    ri;
		ssize_t   only = -1;
		atom_ctx  qa;
		atom_ctx *qq   = ca;

		if (ca->REPO != NULL && ca->REPO[0] == '@' &&
				qm_nbinrepos > 0) {
			size_t      k;
			const char *tok = ca->REPO + 1;

			while (tok[0] == '@')
				tok++;
			for (k = 0; k < qm_nbinrepos; k++) {
				const char *rn = qm_binrepos[k].name;

				while (rn[0] == '@')
					rn++;
				if (strcmp(rn, tok) == 0) {
					only    = (ssize_t)k;
					qa      = *ca;
					qa.REPO = NULL;
					qq      = &qa;
					break;
				}
			}
		}

		for (ri = 0; ri < rcnt; ri++) {
			tree_ctx     *bt = qm_bintree(ri);
			array        *t;
			size_t        cn;
			tree_pkg_ctx *cand;
			tree_pkg_ctx *hitc = NULL;
			size_t        rj;
			bool          seen = false;

			if (only >= 0 && ri != (size_t)only)
				continue;
			if (bt == NULL)
				continue;
			for (rj = 0; rj < ri; rj++)
				if (qm_bintrees[rj] == bt)
					seen = true;
			if (seen)
				continue;
			t = tree_match_atom(bt, qq,
					TREE_MATCH_SORT | TREE_MATCH_VIRTUAL |
					TREE_MATCH_ACCT);
			array_for_each(t, cn, cand) {
				char *pp = tree_pkg_meta(cand, Q_PATH);

				if (pp != NULL && strcmp(pp, want) == 0) {
					hitc = cand;
					break;
				}
			}
			array_free(t);
			if (hitc != NULL)
				return hitc;
		}
	}
	return best_version(ca, BV_BINPKG);
}

static void
qm_soname_iter(const char *blob,
			   void (*fn)(const char *cat, const char *soname, void *priv),
			   void *priv)
{
	const char *p        = blob;
	char        cat[128] = "";

	while (p != NULL && *p != '\0') {
		const char *e;
		size_t      len;

		while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r')
			p++;
		if (*p == '\0')
			break;
		e = p;
		while (*e != '\0' && *e != ' ' && *e != '\t' &&
				*e != '\n' && *e != '\r')
			e++;
		len = (size_t)(e - p);
		if (p[len - 1] == ':') {
			if (len > 1)
				snprintf(cat, sizeof(cat), "%.*s",
						 (int)MIN(len - 1, sizeof(cat) - 1), p);
		} else if (cat[0] != '\0') {
			char son[256];

			snprintf(son, sizeof(son), "%.*s",
					 (int)MIN(len, sizeof(son) - 1), p);
			fn(cat, son, priv);
		}
		p = e;
	}
}

static void
qm_sweep_prov_cb(const char *cat, const char *soname, void *priv)
{
	set  *prov = priv;
	char  key[512];

	snprintf(key, sizeof(key), "%s\1%s", cat, soname);
	add_set(key, prov);
	snprintf(key, sizeof(key), "\1%s", soname);
	add_set(key, prov);
}

struct qm_sweep_req {
	set        *prov;
	array      *missing;
	const char *cpvp;
};

static void
qm_sweep_req_cb(const char *cat, const char *soname, void *priv)
{
	struct qm_sweep_req *sr = priv;
	char                 key[512];
	char                *msg;

	snprintf(key, sizeof(key), "%s\1%s", cat, soname);
	if (contains_set(key, sr->prov) != NULL)
		return;
	snprintf(key, sizeof(key), "\1%s", soname);
	if (contains_set(key, sr->prov) != NULL)
		return;
	xasprintf(&msg, "=%s requires %s (%s): no installed, planned, "
			  "or preserved provider", sr->cpvp, soname, cat);
	array_append(sr->missing, msg);
}

/* verify every planned binpkg's REQUIRES sonames against the providers.
 * visible once the merge list applies: installed libraries, PROVIDES of
 * the planned packages themselves, and the preserved registry.
 * Warn-only by default (REQUIRES metadata is not guaranteed complete,
 * portage --ignore-soname-deps defaults to ignore for the some reason).
 * QMERGE_SONAME_DEPS=hold sets a dangling soname to refusal.
 * We know this movement will cost us a little performance, but it needs
 * to be done. */
static bool
qm_soname_sweep(array *merge)
{
	const char  *mode = qm_config_var("QMERGE_SONAME_DEPS");
	bool         hold;
	set         *prov;
	array       *missing;
	linkage_map *map;
	size_t       i;
	char        *cpvp;
	bool         ok = true;

	if (mode != NULL &&
			(strcmp(mode, "n") == 0 || strcmp(mode, "0") == 0 ||
			 strcmp(mode, "off") == 0))
		return true;
	if (array_cnt(merge) == 0)
		return true;
	hold = mode != NULL &&
			(strcmp(mode, "hold") == 0 || strcmp(mode, "y") == 0 ||
			 strcmp(mode, "1") == 0);

	prov    = create_set();
	missing = array_new();
	map     = qm_linkage_build();
	{
		size_t       pi;
		size_t       oi;
		linkage_pkg *lp;
		linkage_obj *lo;
		char         key[512];

		array_for_each(linkage_pkgs(map), pi, lp)
			array_for_each(lp->objs, oi, lo) {
				if (lo->soname[0] == '\0')
					continue;
				snprintf(key, sizeof(key), "%s\1%s",
						 lo->cat, lo->soname);
				add_set(key, prov);
				snprintf(key, sizeof(key), "\1%s", lo->soname);
				add_set(key, prov);
			}
	}
	linkage_free(map);
	{
		preserved_entry *pe;
		size_t           n;
		char            *pt;
		char             key[512];

		array_for_each(preserved_entries(qm_preserved_get()), i, pe)
			array_for_each(pe->paths, n, pt) {
				const char *bn = strrchr(pt, '/');

				bn = bn != NULL ? bn + 1 : pt;
				snprintf(key, sizeof(key), "\1%s", bn);
				add_set(key, prov);
			}
	}
	array_for_each(merge, i, cpvp) {
		atom_ctx     *a;
		tree_pkg_ctx *bpkg;
		char          exact[520];
		char         *blob;

		snprintf(exact, sizeof(exact), "=%s", cpvp);
		a = atom_explode(exact);
		if (a == NULL)
			continue;
		bpkg = qm_plan_pick(cpvp, a);
		if (bpkg != NULL &&
				(blob = tree_pkg_meta(bpkg, Q_PROVIDES)) != NULL)
			qm_soname_iter(blob, qm_sweep_prov_cb, prov);
		atom_implode(a);
	}
	array_for_each(merge, i, cpvp) {
		atom_ctx            *a;
		tree_pkg_ctx        *bpkg;
		char                 exact[520];
		char                *blob;
		struct qm_sweep_req  sr;

		snprintf(exact, sizeof(exact), "=%s", cpvp);
		a = atom_explode(exact);
		if (a == NULL)
			continue;
		bpkg = qm_plan_pick(cpvp, a);
		if (bpkg != NULL &&
				(blob = tree_pkg_meta(bpkg, Q_REQUIRES)) != NULL) {
			sr.prov    = prov;
			sr.missing = missing;
			sr.cpvp    = cpvp;
			qm_soname_iter(blob, qm_sweep_req_cb, &sr);
		}
		atom_implode(a);
	}
	free_set(prov);

	if (array_cnt(missing) > 0 && !qm_user_quiet) {
		char *m;

		printf("\n%s!!!%s The following packages require sonames "
			   "nothing will provide:\n", hold ? RED : YELLOW, NORM);
		array_for_each(missing, i, m)
			printf("    %s\n", m);
		printf("\n");
	}
	if (hold && array_cnt(missing) > 0)
		ok = false;
	array_deepfree(missing, free);
	return ok;
}

static bool
qm_plan_check_one(const char *cpvp, atom_ctx *pos, set *use,
				  const char *exclude_cpv, char *hit, size_t hitsz)
{
	char          ex[520];
	atom_ctx     *ca;
	tree_pkg_ctx *c;
	bool          ok;

	if (exclude_cpv != NULL && strcmp(cpvp, exclude_cpv) == 0)
		return false;
	snprintf(ex, sizeof(ex), "=%s", cpvp);
	ca = atom_explode(ex);
	if (ca == NULL)
		return false;
	c  = qm_plan_pick(cpvp, ca);
	ok = (c != NULL && atom_satisfied_by(pos, c, use));
	atom_implode(ca);
	if (ok && hit != NULL)
		snprintf(hit, hitsz, "%s", cpvp);
	return ok;
}

/* sweep-scoped: merge-list cpvs bucketed by cat/pn, so an atom only tests the
 * handful of merge-list members it could possibly match instead of the whole
 * list (quadratic on @world-sized merge lists) */
static hash_t *qm_plan_buckets = NULL;

/* resolve-scoped memo of frozen-tree verdicts, keyed by the exact
 * inputs (atom, revdep USE, provider kind); both trees are immutable
 * during resolution so a verdict can never change across sweeps */
static hash_t *qm_verdict_memo = NULL;

/* need docs here @francoisb */
static void
qm_verdict_memo_flush(void)
{
	if (qm_verdict_memo != NULL) {
		hash_free(qm_verdict_memo);
		qm_verdict_memo = NULL;
	}
}

static bool
qm_plan_has_match(array *merge, atom_ctx *pos, set *use,
				  const char *exclude_cpv, char *hit, size_t hitsz)
{
	size_t  i;
	char   *cpvp;

	if (qm_plan_buckets != NULL &&
			pos->CATEGORY != NULL && pos->PN != NULL) {
		char   cpn[512];
		array *bucket;

		snprintf(cpn, sizeof(cpn), "%s/%s", pos->CATEGORY, pos->PN);
		bucket = hash_get(qm_plan_buckets, cpn);
		if (bucket == NULL)
			return false;
		array_for_each(bucket, i, cpvp)
			if (qm_plan_check_one(cpvp, pos, use, exclude_cpv, hit, hitsz))
				return true;
		return false;
	}

	array_for_each(merge, i, cpvp)
		if (qm_plan_check_one(cpvp, pos, use, exclude_cpv, hit, hitsz))
			return true;
	return false;
}

/* is the resolution's package for cpv a FRESH install (its slot holds nothing yet)?
 * used to fire a blocker only when the resolution actually creates the co-install --
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
 * slot the resolution does NOT replace, still satisfy pos? A slotless atom can be
 * met by any slot, so we enumerate every installed version across slots and
 * keep the survivors. Presumably safe outside the vdb enumeration (tree_match re-queries). */
static bool
qm_surviving_installed_satisfies(atom_ctx *pos, set *planned, set *use)
{
	char          cpn[512];
	atom_ctx     *ca;
	array        *all;
	size_t        n;
	tree_pkg_ctx *m;
	bool          ok = false;

	if (pos->CATEGORY == NULL || pos->PN == NULL || qmerge_vdb_tree == NULL)
		return false;
	snprintf(cpn, sizeof(cpn), "%s/%s", pos->CATEGORY, pos->PN);
	ca = atom_explode(cpn);
	if (ca == NULL)
		return false;
	all = tree_match_atom(qmerge_vdb_tree, ca, TREE_MATCH_DEFAULT);
	if (all != NULL) {
		array_for_each(all, n, m) {
			atom_ctx *ma = tree_pkg_atom(m, true);
			char      cps[512];

			snprintf(cps, sizeof(cps), "%s/%s:%s",
					ma->CATEGORY ? : "", ma->PN ? : "", ma->SLOT ? : "");
			if (contains_set(cps, planned) != NULL)
				/* this slot is being replaced by the plan
				 * which goddamn plan? */
				continue;
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
 * groups, but skip `|| ( )` any-of groups entirely. The* alternatives are not
 * individually required, so flattening them into edges invents conflicts (perl
 * virtuals declare `|| ( =perl-5.42* =perl-5.40* ... )`, treating each slot as
 * required fires spurious strands). Presumably safe under-approx: we may miss a conflict
 * where EVERY alternative fails, but never manufactured one.
 * This needs a careful refactoring, portage-parity here can help in not very
 * helpful case.*/
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
		break;
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
 * at a cat/pn:slot the resolution is about to change, so phase B can resolve it
 * OUTSIDE the vdb enumeration (best_version here would re-enter the tree we're
 * iterating and invalidate ctxs).
 * RDEPEND only: a DEPEND-only := is already baked into a built binpkg. */
static int
qm_vdb_freeze_cb(tree_pkg_ctx *pkg, void *priv);

/* one parsed+USE-pruned RDEPEND atom of an installed pkg */
struct qm_vdep {
	char *atomstr;
	char *cpslot; 
	char *cpn;
	int   is_blocker;
	int   hard;
	int   has_slot;
};

struct qm_vpkg {
	char  *revdep;
	char  *cpslot;
	char  *cusestr;
	array *deps;
};

/* frozen vartree method. every installed pkg's pruned RDEPEND, parsed once per
 * resolve and reused by every sweep/backtrack round. Portage resolves
 * against the same kind of snapshot (FakeVartree);the VDB cannot
 * change during resolution: package moves apply before, merges happen
 * after the merge list is final. */
static array *qm_vdb_frozen = NULL;

static int
qm_vdb_freeze_cb(tree_pkg_ctx *pkg, void *priv)
{
	array           *out = priv;
	atom_ctx        *pa  = tree_pkg_atom(pkg, true);
	char             key[512];
	char            *d;
	char            *usestr;
	dep_node_t      *tree;
	array           *atoms;
	size_t           i;
	atom_ctx        *A;
	struct qm_vpkg  *vp;

	d = tree_pkg_meta(pkg, Q_RDEPEND);
	if (d == NULL || *d == '\0')
		return 0;
	tree = dep_grow_tree(d);
	if (tree == NULL)
		return 0;
	snprintf(key, sizeof(key), "%s/%s:%s",
			pa->CATEGORY ? : "", pa->PN ? : "", pa->SLOT ? : "");
	usestr = tree_pkg_meta(pkg, Q_USE);
	{
		set *puse = usedep_flags_to_set(usestr ? : "");
		/* drop inactive USE-conditional deps */
		dep_prune_use(tree, puse);
		free_set(puse);
	}
	atoms = array_new();
	qm_collect_required_atoms(tree, atoms);
	if (array_cnt(atoms) == 0) {
		array_free(atoms);
		dep_burn_tree(tree);
		return 0;
	}
	vp = xzalloc(sizeof(*vp));
	vp->revdep = xstrdup(atom_format("%[CAT]%[PF]", pa));
	vp->cpslot   = xstrdup(key);
	vp->cusestr  = xstrdup(usestr ? : "");
	vp->deps     = array_new();
	array_for_each(atoms, i, A) {
		struct qm_vdep *vd;

		/* ^ antislot etc: skip; ! / !! recorded in positive form */
		if (A->blocker != ATOM_BL_NONE &&
				A->blocker != ATOM_BL_BLOCK &&
				A->blocker != ATOM_BL_BLOCK_HARD)
			continue;
		if (A->blocker != ATOM_BL_NONE) {
			atom_blocker save = A->blocker;

			vd = xzalloc(sizeof(*vd));
			A->blocker     = ATOM_BL_NONE;
			vd->atomstr    = xstrdup(atom_to_string(A));
			vd->is_blocker = 1;
			vd->hard       = (save == ATOM_BL_BLOCK_HARD);
			A->blocker     = save;
		} else {
			char t[512];

			if (A->CATEGORY == NULL || A->PN == NULL)
				continue;
			vd = xzalloc(sizeof(*vd));
			vd->atomstr = xstrdup(atom_to_string(A));
			snprintf(t, sizeof(t), "%s/%s", A->CATEGORY, A->PN);
			vd->cpn = xstrdup(t);
			if (A->SLOT != NULL) {
				vd->has_slot = 1;
				snprintf(t, sizeof(t), "%s/%s:%s",
						A->CATEGORY, A->PN, A->SLOT);
				vd->cpslot = xstrdup(t);
			}
		}
		array_append(vp->deps, vd);
	}
	array_free(atoms);
	dep_burn_tree(tree);
	if (array_cnt(vp->deps) == 0) {
		free(vp->revdep);
		free(vp->cpslot);
		free(vp->cusestr);
		array_free(vp->deps);
		free(vp);
		return 0;
	}
	array_append(out, vp);
	return 0;
}

/* per-round: project the frozen vartree onto the current resolution, applying
 * exactly the filters the old per-round VDB enumeration applied */
static void
qm_edges_from_frozen(struct qm_scctx *sc)
{
	size_t          i;
	size_t          j;
	struct qm_vpkg *vp;
	struct qm_vdep *vd;

	array_for_each(qm_vdb_frozen, i, vp) {
		/* a pkg the resolution itself (re)installs is handled by the
		 * intra-list sweep */
		if (contains_set(vp->cpslot, sc->planned) != NULL)
			continue;
		array_for_each(vp->deps, j, vd) {
			struct qm_edge *e;

			if (!vd->is_blocker) {
				/* slotless version edge (1c): met by any slot, record
				 * it only if the resolution touches this cat/pn at all */
				if (!vd->has_slot) {
					if (contains_set(vd->cpn, sc->planned_cpn) == NULL)
						continue;
				} else if (contains_set(vd->cpslot, sc->planned) == NULL)
					continue;
			}
			e = xmalloc(sizeof(*e));
			e->revdep   = xstrdup(vp->revdep);
			e->atomstr    = xstrdup(vd->atomstr);
			e->cusestr    = xstrdup(vp->cusestr);
			e->is_blocker = vd->is_blocker;
			e->hard       = vd->hard;
			e->slotless   = !vd->is_blocker && !vd->has_slot;
			e->revdep_cpslot = xstrdup(vp->cpslot);
			array_append(sc->edges, e);
		}
	}
}

/* Resolve the complete end-state graph and refuse a resolution that would strand a
 * package we can't rebuild from a binpkg.
 * End-state = (installed pkgs the resolution doesn't replace) + (planned binpkgs).
 * For every RDEPEND edge of every end-state pkg that points at a cat/pn:slot
 * the resolution changes, check the planned version still satisfies the full atom
 * (version op, slot, subslot, USE). For edges from installed packages we only
 * refuse when the edge worked BEFORE the resolution, matching portage's complete-graph.
 * "initially-satisfied-now-broken" classification, so a pre-existing breakage
 * never blocks a merge. Portage tries to backtrack/rebuild here, and we say nope.
 * Returns the number of conflicts (0 = end-state is consistent). */
static int
qm_check_slot_conflicts(array *merge, set *fixable, hash_t *fix_edges)
{
	struct qm_scctx sc;
	size_t          i;
	char           *cpvp;
	struct qm_edge *e;

	/* cpslot -> cpv, to catch same-slot version dups */
	set *seen = create_set();   

	sc.planned     = create_set();
	sc.planned_cpn = create_set();
	sc.edges       = array_new();
	/* nullable; Layer 2 collects upgrade targets */
	sc.fixable     = fixable;   
	sc.fix_edges   = fix_edges;
	sc.conflicts   = 0;
	sc.printed     = 0;

	qm_plan_buckets = hash_new();

	/* which cat/pn:slot (and bare cat/pn, for 1c) the resolution (re)installs */
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
		 * resolution = contradictory version requirements the forward calculation couldn't
		 * reconcile.
		 * Not fixable by upgrading a revdep, so it never lands in `fixable`. */
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

		/* bucket the plan by cat/pn for qm_plan_has_match (values
		 * borrow the merge array's cpv strings, freed at sweep end) */
		{
			array *bucket = hash_get(qm_plan_buckets, cpn);

			if (bucket == NULL) {
				bucket = array_new();
				qm_plan_buckets =
						hash_add(qm_plan_buckets, cpn, bucket, NULL);
			}
			array_append(bucket, cpvp);
		}
		atom_implode(a);
	}

	/* Sweep 1 phase A: project the frozen vartree onto this resolution (the
	 * freeze itself enumerates the VDB once per resolve, no best_version) */
	if (qmerge_vdb_tree != NULL) {
		if (qm_vdb_frozen == NULL) {
			qm_vdb_frozen = array_new();
			tree_foreach_pkg_fast(qmerge_vdb_tree, qm_vdb_freeze_cb,
								  qm_vdb_frozen, NULL);
		}
		qm_edges_from_frozen(&sc);
	}

	/* Sweep 1 phase B: now safe to resolve providers.
	 * Refuses only if the planned version breaks an edge the installed version satisfied. */
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
		cuse = usedep_flags_to_set(e->cusestr);

		/* blocker: an installed pkg blocks something.
		 * Only fire if the RESOLUTION introduces the blocked pkg,
		 * a pre-existing installed/installed block isn't the resolution's
		 * doing (initially-satisfied logic). */
		if (e->is_blocker) {
			char hit[520];

			/* fire only if the resolution freshly introduces the blocked pkg */
			if (qm_plan_has_match(merge, A, cuse, NULL, hit, sizeof(hit)) &&
				qm_is_fresh_install(hit))
				qm_report_blocker(&sc, e->revdep, e->atomstr, hit,
						e->hard);
			free_set(cuse);
			atom_implode(A);
			continue;
		}

		/* slotless (1c): fire only if it was satisfied before AND nothing in
		 * the end-state (planned, or an installed survivor in any slot) still
		 * satisfies it, i.e. the resolution dropped the last matching version. */
		if (e->slotless) {
			tree_pkg_ctx *mbest = best_version(A, BV_INSTALLED);

			if (mbest != NULL && atom_satisfied_by(A, mbest, cuse) &&
				!qm_plan_has_match(merge, A, cuse, NULL, NULL, 0) &&
				!qm_surviving_installed_satisfies(A, sc.planned, cuse))
				qm_report_conflict(&sc, e->revdep, e->atomstr,
						e->revdep_cpslot);
			free_set(cuse);
			atom_implode(A);
			continue;
		}

		snprintf(cpslot, sizeof(cpslot), "%s/%s:%s",
				A->CATEGORY ? : "", A->PN ? : "", A->SLOT ? : "");
		ca = atom_explode(cpslot);
		if (ca == NULL) { free_set(cuse); atom_implode(A); continue; }

		/* memoized: both trees are frozen during resolution, so the
		 * verdict for (atom, revdep-USE) never changes across
		 * sweeps; identical dep atoms repeat across hundreds of
		 * revdeps on @world-sized merge lists */
		{
			char *mk;
			void *mv;
			bool  conflict;

			if (contains_set(cpslot, sc.planned) != NULL) {
				/* plan-dependent: exact planned instance, no memo */
				conflict = false;
				if (!qm_plan_has_match(merge, A, cuse, NULL, NULL, 0)) {
					oldp = best_version(ca, BV_INSTALLED);
					if (oldp != NULL && atom_satisfied_by(A, oldp, cuse))
						conflict = true;
				}
			} else {
			xasprintf(&mk, "%s\1%s", e->atomstr, e->cusestr);
			mv = qm_verdict_memo != NULL ?
					hash_get(qm_verdict_memo, mk) : NULL;
			if (mv != NULL) {
				conflict = ((intptr_t)mv == 2);
			} else {
				conflict = false;
				/* newp fully consumed before oldp is fetched (ctx
				 * invalidation) */
				newp = best_version(ca, BV_BINPKG);
				if (newp != NULL && !atom_satisfied_by(A, newp, cuse)) {
					oldp = best_version(ca, BV_INSTALLED);
					if (oldp != NULL && atom_satisfied_by(A, oldp, cuse))
						conflict = true;
				}
				if (qm_verdict_memo == NULL)
					qm_verdict_memo = hash_new();
				qm_verdict_memo = hash_add(qm_verdict_memo, mk,
						(void *)(intptr_t)(conflict ? 2 : 1), NULL);
			}
			free(mk);
			}
			if (conflict)
				qm_report_conflict(&sc, e->revdep, e->atomstr,
						e->revdep_cpslot);
		}
		free_set(cuse);
		atom_implode(ca);
		atom_implode(A);
	}

	/* Sweep 2: intra-list edges, a planned revdep's binpkg was built
	 * against a subslot/version the resolution may not be installing (multi-binhost
	 * skew).
	 * End-state provider = planned if planned, else installed.
	 * No initially-satisfied gate: a package's own bindings must hold in the set
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
		p_fresh = qm_is_fresh_install(cpvp);

		tree = dep_grow_tree(prdep);
		if (tree != NULL) {
			cuse  = usedep_flags_to_set(puse);
			/* drop inactive USE-conditional deps */
			dep_prune_use(tree, cuse);
			atoms = array_new();
			/* this skips || ( ) groups */
			qm_collect_required_atoms(tree, atoms);
			array_for_each(atoms, j, A) {
				char          cpslot[512];
				atom_ctx     *ca;
				tree_pkg_ctx *prov;

				/* blocker from a planned pkg: violated if the end-state (an
				 * installed pkg that survives, or another planned pkg) holds a
				 * match. 
				 * A same-slot version being replaced isn't in the
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
								qm_report_blocker(&sc, pcons,
										atom_to_string(A), mcpv,
										save == ATOM_BL_BLOCK_HARD);
							}
						}
					}
					/* planned P blocks another planned pkg: fire if either is a
					 * fresh install (both pre-installed = pre-existing) */
					if (qm_plan_has_match(merge, A, cuse, cpvp,
										  hit, sizeof(hit)) &&
						(p_fresh || qm_is_fresh_install(hit)))
						qm_report_blocker(&sc, pcons, atom_to_string(A),
								hit, save == ATOM_BL_BLOCK_HARD);
					A->blocker = save;
					continue;
				}
				/* ^ antislot: skip */
				if (A->blocker != ATOM_BL_NONE)
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
						/* resolution doesn't touch this cat/pn */
						continue;
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
				{
					char  kind = (contains_set(cpslot, sc.planned) != NULL)
								 ? 'P' : 'I';
					bool  bad;

					if (kind == 'P') {
						/* resolution-dependent: judged against the EXACT
						 * planned instance, and never memoized (the
						 * merge list changes across backtrack rounds) */
						bad = !qm_plan_has_match(merge, A, cuse,
								NULL, NULL, 0);
					} else {
						char *mk;
						void *mv;

						xasprintf(&mk, "%c%s\1%s",
								  kind, atom_to_string(A), puse);
						mv = qm_verdict_memo != NULL ?
								hash_get(qm_verdict_memo, mk) : NULL;
						if (mv != NULL) {
							bad = ((intptr_t)mv == 2);
						} else {
							prov = best_version(ca, BV_INSTALLED);
							bad = (prov != NULL &&
								   !atom_satisfied_by(A, prov, cuse));
							if (qm_verdict_memo == NULL)
								qm_verdict_memo = hash_new();
							qm_verdict_memo = hash_add(qm_verdict_memo,
									mk,
									(void *)(intptr_t)(bad ? 2 : 1),
									NULL);
						}
						free(mk);
					}
					if (bad)
						qm_report_conflict(&sc, pcons, atom_to_string(A),
								pcons_cpslot);
				}
				atom_implode(ca);
			}
			/* tree-owned atoms; free only the container */
			array_free(atoms);
			free_set(cuse);
			dep_burn_tree(tree);
		}
		free(pcons);
		free(pcons_cpslot);
		free(prdep);
		free(puse);
	}

	{
		array *bvals = hash_values(qm_plan_buckets);
		void  *bv;

		array_for_each(bvals, i, bv)
			array_free((array *)bv);
		array_free(bvals);
		hash_free(qm_plan_buckets);
		qm_plan_buckets = NULL;
	}

	array_for_each(sc.edges, i, e) {
		free(e->revdep);
		free(e->atomstr);
		free(e->cusestr);
		free(e->revdep_cpslot);
		free(e);
	}
	array_free(sc.edges);
	free_set(sc.planned);
	free_set(sc.planned_cpn);
	free_set(seen);
	return sc.conflicts;
}

/* Layer 2 (-u): instead of refusing a strand, pull a NEWER binpkg of the
 * stranded revdep (portage would rebuild it; we pull a newer build).
 * That may strand ITS revdeps -> iterate to a fixpoint.
 * Monotone: each step adds a strictly-newer, not-yet-planned version,
 * so it terminates; the cap is only a backstop.
 * Blockers and provider-downgrades never land in `fixable`, so
 * they persist and the caller's sweep refuses on them.
 * Augments plan->merge in place; the loud sweep in the 
 * caller reports whatever is left. Hard safety ceiling over --backtrack s*/
#define QM_MAX_FIXPOINT 64
/* map of cat/pn -> cloned full atom of the provider the resolution installs;
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

	array_deepfree(vals, atom_implode_cb);
	hash_free(map);
}

/* do the candidate's baked subslot pins agree with the planned stack?
 * Only atoms with an explicit SUBSLOT whose provider the resolution touches
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

	cuse = usedep_flags_to_set(tree_pkg_meta(cand, Q_USE));
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

/* find the best repair candidate for a wayward revdep: newest
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
			/* highest-first within repo: first passing = best */
			break;
		}
		array_free(t);
	}
	*repo_out = brepo;
	return best;
}

static int qm_plan_drop(struct qm_plan *plan, const char *cpn);

/* same-version rebuilds pinned to the just-held provider version;
 * keeping them would strand THEM next round, so drop every
 * planned entry whose binpkg pins pcpn at a subslot other 
 * than the installed one */
static int
qm_plan_drop_pinning(struct qm_plan *plan, const char *pcpn,
					 set *todo, int round)
{
	size_t    i;
	int       dropped = 0;
	atom_ctx *ia;
	char      islot[128] = "";

	ia = atom_explode(pcpn);
	if (ia != NULL) {
		tree_pkg_ctx *ip = best_version(ia, BV_INSTALLED);

		if (ip != NULL) {
			atom_ctx *ipa = tree_pkg_atom(ip, true);

			snprintf(islot, sizeof(islot), "%s",
					 ipa->SUBSLOT ? : (ipa->SLOT ? : ""));
		}
		atom_implode(ia);
	}
	if (islot[0] == '\0')
		return 0;

	for (i = array_cnt(plan->merge); i > 0; ) {
		i--;
		char         *cpvp = array_get(plan->merge, i);
		char          cex[560];
		atom_ctx     *ca;
		atom_ctx     *cba;
		tree_pkg_ctx *bp;
		char         *rdep;
		dep_node_t   *t;
		array        *atoms;
		size_t        j;
		atom_ctx     *A;
		char          ccpn[512];
		bool          disagree = false;

		snprintf(cex, sizeof(cex), "=%s", cpvp);
		ca = atom_explode(cex);
		if (ca == NULL)
			continue;
		bp = best_version(ca, BV_BINPKG);
		if (bp == NULL) {
			atom_implode(ca);
			continue;
		}
		cba = tree_pkg_atom(bp, false);
		snprintf(ccpn, sizeof(ccpn), "%s/%s",
				 cba->CATEGORY ? : "", cba->PN ? : "");
		rdep = tree_pkg_meta(bp, Q_RDEPEND);
		if (rdep != NULL && *rdep != '\0' &&
				(t = dep_grow_tree(rdep)) != NULL) {
			set *cuse = usedep_flags_to_set(tree_pkg_meta(bp, Q_USE) ? : "");

			dep_prune_use(t, cuse);
			atoms = array_new();
			qm_collect_required_atoms(t, atoms);
			array_for_each(atoms, j, A) {
				char acpn[512];

				if (A == NULL || A->SUBSLOT == NULL ||
						A->blocker != ATOM_BL_NONE ||
						A->CATEGORY == NULL || A->PN == NULL)
					continue;
				snprintf(acpn, sizeof(acpn), "%s/%s",
						 A->CATEGORY, A->PN);
				if (strcmp(acpn, pcpn) == 0 &&
						strcmp(A->SUBSLOT, islot) != 0) {
					disagree = true;
					break;
				}
			}
			array_free(atoms);
			free_set(cuse);
			dep_burn_tree(t);
		}
		atom_implode(ca);
		if (disagree) {
			atom_ctx *ta = atom_explode(ccpn);
			bool      is_target = ta != NULL &&
					qm_atom_is_target(ta, todo);

			if (ta != NULL)
				atom_implode(ta);
			if (!is_target && qm_plan_drop(plan, ccpn) > 0) {
				char msg[1100];

				dropped++;
				snprintf(msg, sizeof(msg),
						 "dropped: rebuilt against a %s version that "
						 "is held back (backtrack round %d)",
						 pcpn, round);
				qm_notice(ccpn, msg);
			}
		}
	}
	return dropped;
}

/* drop every merge-list entry of cat/pn (hold-back: keep the installed
 * version instead of the planned upgrade) */
static int
qm_plan_drop(struct qm_plan *plan, const char *cpn)
{
	size_t i;
	int    dropped = 0;

	for (i = array_cnt(plan->merge); i > 0; ) {
		i--;
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
	/* cat/pn already held back */
	set *held   = create_set();

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

		/* quiet sweep (fixable != NULL): collect dangling / left behind revdeps */
		(void)qm_check_slot_conflicts(plan->merge, fixable, fix_edges);
		if (cnt_set(fixable) == 0) {
			array *ev = hash_values(fix_edges);

			array_deepfree(ev, set_free_cb);
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
			/* strategy A: a rebuilt revdep whose baked pins agree
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
					qm_internal_pull = true;
					qm_resolve(ea, NULL, plan, 0);
					qm_internal_pull = false;
					atom_implode(ea);
					progress = true;
					if (verbose) {
						char msg[560];
						char key[560];

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
				}
			} else if (newc == NULL) {
				/* strategy B: no rebuilt revdep exists anywhere.
				 * Lenient (default): keep the provider upgrade and
				 * tolerate the dangling pin, warning like portage.
				 * Strict: hold the provider back at its installed
				 * version and drop planned rebuilds that pin the new
				 * one, unless the user explicitly asked for it. */
				set   *es = hash_get(fix_edges, cpslot);
				array *ek = es != NULL ? set_keys(es) : NULL;
				size_t ei;
				char  *astr;

				if (qm_lenient && ek != NULL) {
					array_for_each(ek, ei, astr) {
						char tk[1024];

						snprintf(tk, sizeof(tk), "%s\1%s", cpslot, astr);
						if (qm_tolerated == NULL)
							qm_tolerated = create_set();
						if (contains_set(tk, qm_tolerated) == NULL) {
							char msg[560];

							add_set(tk, qm_tolerated);
							progress = true;
							snprintf(msg, sizeof(msg),
									 "pin %s left unsatisfied, no "
									 "acceptable rebuilt binpkg "
									 "(lenient, backtrack round %d; "
									 "QMERGE_LENIENT_UPGRADE=0 holds "
									 "the provider back instead)",
									 astr, iter + 1);
							qm_notice(cpslot, msg);
						}
					}
				} else if (ek != NULL)
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
								 "installed revdeps pin it and no "
								 "rebuilt binpkgs exist (backtrack "
								 "round %d; QMERGE_LENIENT_UPGRADE=1 "
								 "upgrades it instead)", iter + 1);
						qm_notice(key, msg);
						/* consistency: planned same-version rebuilds
						 * pinned to the held-back version would strand
						 * next, drop them too */
						qm_plan_drop_pinning(plan, pcpn, todo, iter + 1);
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

			array_deepfree(ev, set_free_cb);
			hash_free(fix_edges);
		}
		qm_planned_map_free(pinmap);

		if (!progress && array_cnt(plan->merge) == before)
			/* stuck: remaining conflicts are genuine
			 * hopefully we will have a automated mechanism
			 * to somewhat construct a safe-enforcable bypass
			 * to some of the conflicts here, and have a sort of
			 * debian-like compatibility in installing from
			 * different repositories  */
			break;
		used = iter + 1;
	}

	free_set(held);
	/* preview companion line: the pretend/dry-run path runs with
	 * quiet=1 yet still prints the merge list, so no quiet check here */
	if (used > 0)
		printf(">>> Backtracked %d round(s) to repair dependency "
			   "conflicts\n", used);
}

/* resolve the requested atoms into a dependency-ordered merge list, then
 * fetch+merge each package deps-first.
 * pretend/fetch modes flow through pkg_fetch 
 * (which prints in pretend and skips merge for --fetchonly). */
/* Layer 3 (same-slot unification) helpers.
 * A resolution holding two versions of one cat/pn:slot is portage's slot conflict.
 * Portage masks/removes/blocks one side and re-resolves after.
 * These collect the colliding pairs, score both sides against every 
 * recorded demand, and pick the side to mask/block.
 * The driver loops the re-resolve within the --backtrack runs. */

static array *
qm_collect_slot_dups(array *merge, set **planned_out)
{
	array  *dups    = array_new();
	set    *seen    = create_set();
	set    *done    = create_set();
	set    *planned = create_set();
	size_t  i;
	char   *cpvp;

	array_for_each(merge, i, cpvp) {
		char          ex[560];
		atom_ctx     *a;
		tree_pkg_ctx *bpkg;
		atom_ctx     *ba;
		char          cpslot[512];
		const char   *prev;

		snprintf(ex, sizeof(ex), "=%s", cpvp);
		a = atom_explode(ex);
		if (a == NULL)
			continue;
		bpkg = best_version(a, BV_BINPKG);
		if (bpkg == NULL) { atom_implode(a); continue; }
		ba = tree_pkg_atom(bpkg, true);
		snprintf(cpslot, sizeof(cpslot), "%s/%s:%s",
				 ba->CATEGORY ? : "", ba->PN ? : "", ba->SLOT ? : "");
		add_set(cpslot, planned);
		prev = get_set(cpslot, seen);
		if (prev != NULL && strcmp(prev, cpvp) != 0 &&
				contains_set(cpslot, done) == NULL) {
			char *rec;

			xasprintf(&rec, "%s\1%s\1%s", cpslot, prev, cpvp);
			array_append(dups, rec);
			add_set(cpslot, done);
		} else if (prev == NULL) {
			add_set_value(cpslot, (void *)cpvp, NULL, seen);
		}
		atom_implode(a);
	}
	free_set(seen);
	free_set(done);
	*planned_out = planned;
	return dups;
}

/* every demand on cpslot: the forward descent's records plus the pruned
 * RDEPENDs of installed revdeps the resolution does NOT replace (a replaced
 * revdep's successor recorded its own demands) */
static array *
qm_unify_demands_for(const char *cpslot, set *planned)
{
	array  *out = array_new();
	array  *d   = qm_demands != NULL ? hash_get(qm_demands, cpslot) : NULL;
	size_t  i;
	char   *rec;
	char    cpn[512];
	char   *cl;

	if (d != NULL)
		array_for_each(d, i, rec)
			array_append(out, xstrdup(rec));
	snprintf(cpn, sizeof(cpn), "%s", cpslot);
	cl = strchr(cpn, ':');
	if (cl != NULL)
		*cl = '\0';
	if (qm_vdb_frozen != NULL) {
		struct qm_vpkg *vp;
		size_t          j;
		struct qm_vdep *vd;

		array_for_each(qm_vdb_frozen, i, vp) {
			if (contains_set(vp->cpslot, planned) != NULL)
				continue;
			array_for_each(vp->deps, j, vd) {
				if (vd->is_blocker || vd->cpn == NULL)
					continue;
				if (strcmp(vd->cpn, cpn) != 0)
					continue;
				if (vd->has_slot && vd->cpslot != NULL &&
						strcmp(vd->cpslot, cpslot) != 0)
					continue;
				xasprintf(&rec, "%s\1%s", vp->revdep, vd->atomstr);
				array_append(out, rec);
			}
		}
	}
	return out;
}

/* fill v[i] with does-cpvp-satisfy-demand-i. 
 * geetting false = no such candidate */
static bool
qm_unify_sat_vec(const char *cpvp, array *dm, bool *v)
{
	char          ex[560];
	atom_ctx     *ca;
	tree_pkg_ctx *cand;
	size_t        i;
	char         *rec;

	snprintf(ex, sizeof(ex), "=%s", cpvp);
	ca = atom_explode(ex);
	if (ca == NULL)
		return false;
	cand = qm_plan_pick(cpvp, ca);
	if (cand == NULL) {
		atom_implode(ca);
		return false;
	}
	array_for_each(dm, i, rec) {
		char     *sep = strchr(rec, '\1');
		atom_ctx *A   = sep != NULL ? atom_explode(sep + 1) : NULL;

		if (A == NULL)
			continue;
		v[i] = atom_satisfied_by(A, cand, NULL);
		atom_implode(A);
	}
	atom_implode(ca);
	return true;
}

/* missed demands for this side of the pair.
 * -1 means candidate is gone.
 * if this failsafe mechanism works, we're the winners. */
static int
qm_unify_score(const char *cpslot, const char *cpvp, set *planned)
{
	array  *dm   = qm_unify_demands_for(cpslot, planned);
	size_t  n    = array_cnt(dm);
	bool   *v    = xzalloc(n * sizeof(bool) + 1);
	int     miss = 0;
	size_t  i;

	if (!qm_unify_sat_vec(cpvp, dm, v)) {
		miss = -1;
	} else {
		for (i = 0; i < n; i++)
			if (!v[i])
				miss++;
	}
	free(v);
	array_deepfree(dm, free);
	return miss;
}

/* pick the side of one collision to mask. */
static int
qm_unify_arbitrate(const char *dup, set *planned, set *todo, set *nofix,
				   char *maskkey, size_t mklen, char *altkey, size_t aklen,
				   char *outslot, size_t oslen)
{
	char     *buf = xstrdup(dup);
	char     *cpslot;
	char     *ca;
	char     *cb;
	char     *s;
	char      exa[560];
	char      exb[560];
	atom_ctx *aa  = NULL;
	atom_ctx *ab  = NULL;
	bool      prota;
	bool      protb;
	int       ret = -1;

	cpslot = buf;
	s = strchr(buf, '\1');
	if (s == NULL) { free(buf); return -1; }
	*s = '\0';
	ca = s + 1;
	s = strchr(ca, '\1');
	if (s == NULL) { free(buf); return -1; }
	*s = '\0';
	cb = s + 1;

	if (contains_set(cpslot, nofix) != NULL) {
		free(buf);
		return -1;
	}
	snprintf(exa, sizeof(exa), "=%s", ca);
	snprintf(exb, sizeof(exb), "=%s", cb);
	aa = atom_explode(exa);
	ab = atom_explode(exb);
	if (aa == NULL || ab == NULL || aa->PVR == NULL || ab->PVR == NULL)
		goto out;
	/* a version mask cannot
	 * separate the two same versions, leave it to the refusal */
	if (strcmp(aa->PVR, ab->PVR) == 0) {
		add_set(cpslot, nofix);
		goto out;
	}
	prota = qm_atom_is_target(aa, todo);
	protb = qm_atom_is_target(ab, todo);
	if (prota && protb) {
		add_set(cpslot, nofix);
		goto out;
	}
	{
		const atom_ctx *keep;
		const atom_ctx *lose;
		const char     *keepcpv;
		const char     *losecpv;

		if (prota) {
			keep = aa; lose = ab; keepcpv = ca; losecpv = cb;
		} else if (protb) {
			keep = ab; lose = aa; keepcpv = cb; losecpv = ca;
		} else {
			int sa = qm_unify_score(cpslot, ca, planned);
			int sb = qm_unify_score(cpslot, cb, planned);

			if (sa < 0 && sb < 0) {
				add_set(cpslot, nofix);
				goto out;
			}
			if (sb < 0 || (sa >= 0 && sa < sb)) {
				keep = aa; lose = ab; keepcpv = ca; losecpv = cb;
			} else if (sa < 0 || sb < sa) {
				keep = ab; lose = aa; keepcpv = cb; losecpv = ca;
			} else if (atom_compare_flg(aa, ab,
					ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO) == NEWER) {
				keep = aa; lose = ab; keepcpv = ca; losecpv = cb;
			} else {
				keep = ab; lose = aa; keepcpv = cb; losecpv = ca;
			}
		}
		snprintf(maskkey, mklen, "%s/%s-%s",
				 lose->CATEGORY ? : "", lose->PN ? : "", lose->PVR);
		/* a protected side must never become the fallback mask */
		if (prota || protb)
			altkey[0] = '\0';
		else
			snprintf(altkey, aklen, "%s/%s-%s",
					 keep->CATEGORY ? : "", keep->PN ? : "", keep->PVR);
		snprintf(outslot, oslen, "%s", cpslot);
		{
			char msg[560];

			snprintf(msg, sizeof(msg),
					 "slot conflict with %s in %s: masked and "
					 "re-resolving (backtrack)", keepcpv, cpslot);
			qm_notice(losecpv, msg);
		}
		ret = 0;
	}
out:
	if (aa != NULL)
		atom_implode(aa);
	if (ab != NULL)
		atom_implode(ab);
	free(buf);
	return ret;
}

/* unification lets Jesus take the wheel: per remaining collision show 
 * who wants which side. best we can do. */
static void
qm_print_dup_demands(array *dups, set *planned)
{
	size_t di;
	char  *dq;

	array_for_each(dups, di, dq) {
		char   *buf = xstrdup(dq);
		char   *cpslot;
		char   *ca;
		char   *cb;
		char   *s;
		array  *dm;
		size_t  n;
		size_t  i;
		char   *rec;
		bool   *sata;
		bool   *satb;
		int     either = 0;

		cpslot = buf;
		s = strchr(buf, '\1');
		if (s == NULL) { free(buf); continue; }
		*s = '\0';
		ca = s + 1;
		s = strchr(ca, '\1');
		if (s == NULL) { free(buf); continue; }
		*s = '\0';
		cb = s + 1;

		dm   = qm_unify_demands_for(cpslot, planned);
		n    = array_cnt(dm);
		sata = xzalloc(n * sizeof(bool) + 1);
		satb = xzalloc(n * sizeof(bool) + 1);
		(void)qm_unify_sat_vec(ca, dm, sata);
		(void)qm_unify_sat_vec(cb, dm, satb);
		warn("slot conflict: both %s and %s land in slot %s, wanted by:",
			 ca, cb, cpslot);
		array_for_each(dm, i, rec) {
			char *sep = strchr(rec, '\1');

			if (sep == NULL)
				continue;
			*sep = '\0';
			if (sata[i] && satb[i]) {
				either++;
			} else if (sata[i] != satb[i]) {
				warn("    %s requires %s -> only %s",
					 rec, sep + 1, sata[i] ? ca : cb);
			} else {
				warn("    %s requires %s -> satisfied by neither side",
					 rec, sep + 1);
			}
		}
		if (either > 0)
			warn("    (and %d demand%s either side satisfies)",
				 either, either == 1 ? "" : "s");
		free(sata);
		free(satb);
		array_deepfree(dm, free);
		free(buf);
	}
}

/* strand/blocker/collision count of the current resolution, without output */
static int
qm_quiet_conflict_count(array *merge)
{
	set    *tf = create_set();
	hash_t *te = hash_new();
	int     n  = qm_check_slot_conflicts(merge, tf, te);
	array  *ev = hash_values(te);

	array_deepfree(ev, set_free_cb);
	hash_free(te);
	free_set(tf);
	return n;
}


/* blocker related collection stuff here */
static int
qm_blk_sweep(array *merge)
{
	qm_blk_reset();
	qm_blk_collect = true;
	(void)qm_quiet_conflict_count(merge);
	qm_blk_collect = false;
	return qm_check_slot_conflicts(merge, NULL, NULL);
}

/* The actual mechanism from portage applied here. Under --keep-going it
 * runs in a forked child (qm_kg_round) that reports each package over
 * the round pipe and fails on the first failure instead of going through. */
static int
qm_exec_round(struct qm_plan *plan)
{
	size_t  i;
	char   *cpvp;
	int     rc = EXIT_SUCCESS;

	qm_print_use_rejects();
	/* QMERGE_BLOCKERS feature: drop the soft-blocked installed packages the resolution
	 * supersedes before merging (with -U, which ideally is safe).
	 * This is the only place the resolver unmerges a package the user
	 * did not name. */
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
	/* yank everything down concurrently first. */
	if (qmerge_prefetch)
		qm_prefetch(plan->merge, qmerge_jobs);

	array_for_each(plan->merge, i, cpvp) {
		atom_ctx     *a;
		tree_pkg_ctx *bpkg;
		char          exact[520];

		snprintf(exact, sizeof(exact), "=%s", cpvp);
		a = atom_explode(exact);
		if (a == NULL)
			continue;
		bpkg = qm_plan_pick(cpvp, a);
		qm_mg_n     = i + 1;
		qm_mg_total = array_cnt(plan->merge);
		if (bpkg != NULL) {
			if (qm_kg_child) {
				atom_ctx *fa  = tree_pkg_atom(bpkg, true);
				size_t    pre = qm_exec_failed != NULL ?
						cnt_set(qm_exec_failed) : 0;

				qm_kg_announce('B', cpvp,
							   fa != NULL ? fa->SLOT : NULL);
				pkg_fetch(0, a, bpkg);
				if ((qm_exec_failed != NULL ?
						cnt_set(qm_exec_failed) : 0) > pre) {
					qm_kg_announce('S', cpvp, NULL);
					atom_implode(a);
					exit(100);
				}
				qm_kg_announce('O', cpvp, NULL);
			} else {
				pkg_fetch(0, a, bpkg);
			}
		} else {
			warn("resolved package %s not found as a binpkg", cpvp);
			qm_exec_fail(a);
			if (qm_kg_child) {
				qm_kg_announce('S', cpvp, NULL);
				atom_implode(a);
				exit(100);
			}
		}
		atom_implode(a);
	}
	qm_mg_n = qm_mg_total = 0;

	if (qm_exec_failed != NULL && cnt_set(qm_exec_failed) > 0) {
		array  *fk = set_keys(qm_exec_failed);
		size_t  fn;
		char   *fp;

		warn("the following %zu package(s) could not be merged:",
			 cnt_set(qm_exec_failed));
		array_sort(fk, qm_strcmp_cb);
		array_for_each(fk, fn, fp)
			warn("  !!! %s", fp);
		array_free(fk);
		rc = EXIT_FAILURE;
	}

	if (!pretend) {
		qm_preserved_gc();
		qm_preserved_finish();
	}
	return rc;
}

/* does dep atom A hit a keep-going mask entry (name or name:slot)
 * name-only dep vs slot-masked entries: any masked slot of the
 * name counts, the resolver already found nothing else */
static bool
qm_kg_atom_masked(const atom_ctx *A)
{
	char key[512];

	if (qm_kg_mask == NULL || A == NULL ||
			A->CATEGORY == NULL || A->PN == NULL)
		return false;
	snprintf(key, sizeof(key), "%s/%s", A->CATEGORY, A->PN);
	if (contains_set(key, qm_kg_mask) != NULL)
		return true;
	if (A->SLOT != NULL) {
		snprintf(key, sizeof(key), "%s/%s:%s",
				 A->CATEGORY, A->PN, A->SLOT);
		return contains_set(key, qm_kg_mask) != NULL;
	} else {

		array  *mk  = set_keys(qm_kg_mask);
		size_t  n;
		char   *m;
		bool    hit = false;
		size_t  kl;

		snprintf(key, sizeof(key), "%s/%s:", A->CATEGORY, A->PN);
		kl = strlen(key);
		array_for_each(mk, n, m)
			if (strncmp(m, key, kl) == 0)
				hit = true;
		array_free(mk);
		return hit;
	}
}

static bool
qm_kg_plan_satisfies(struct qm_plan *plan, const atom_ctx *A)
{
	size_t i;
	char  *cpvp;

	array_for_each(plan->merge, i, cpvp) {
		char          ex[560];
		atom_ctx     *ca;
		tree_pkg_ctx *bp;
		bool          ok = false;

		snprintf(ex, sizeof(ex), "=%s", cpvp);
		ca = atom_explode(ex);
		if (ca == NULL)
			continue;
		bp = best_version(ca, BV_BINPKG);
		if (bp != NULL) {
			atom_ctx *pa = tree_pkg_atom(bp, true);

			ok = pa != NULL && atom_compare(pa, A) == EQUAL;
		}
		atom_implode(ca);
		if (ok)
			return true;
	}
	return false;
}

/* after masking a failed package, sweep the resolution to a
 * fixpoint dropping entries whose runtime deps now resolve to nothing.
 * Dropped pkgnames join the mask so THEIR dependents fall on the next check. */
static int
qm_kg_drop_dependents(struct qm_plan *plan)
{
	static const enum tree_pkg_meta_keys metas[] =
			{ Q_RDEPEND, Q_PDEPEND, Q_IDEPEND };
	bool again   = true;
	int  dropped = 0;

	if (qm_kg_mask == NULL || cnt_set(qm_kg_mask) == 0)
		return 0;
	while (again) {
		size_t i;

		again = false;
		for (i = array_cnt(plan->merge); i > 0; ) {
			i--;
			char         *cpvp = array_get(plan->merge, i);
			char          ex[560];
			atom_ctx     *ca;
			tree_pkg_ctx *bp;
			char          ccpn[512] = "";
			char          why[600]  = "";
			bool          gone = false;
			size_t        mi;

			snprintf(ex, sizeof(ex), "=%s", cpvp);
			ca = atom_explode(ex);
			if (ca == NULL)
				continue;
			bp = best_version(ca, BV_BINPKG);
			if (bp == NULL) {
				atom_implode(ca);
				continue;
			}
			{
				atom_ctx *cba = tree_pkg_atom(bp, false);

				snprintf(ccpn, sizeof(ccpn), "%s/%s",
						 cba->CATEGORY ? : "", cba->PN ? : "");
			}
			for (mi = 0; mi < ARRAY_SIZE(metas) && !gone; mi++) {
				char       *ds = tree_pkg_meta(bp, metas[mi]);
				dep_node_t *t;

				if (ds == NULL || *ds == '\0')
					continue;
				if ((t = dep_grow_tree(ds)) == NULL)
					continue;
				{
					set      *cuse  = usedep_flags_to_set(
							tree_pkg_meta(bp, Q_USE) ? : "");
					array    *atoms = array_new();
					size_t    j;
					atom_ctx *A;

					dep_prune_use(t, cuse);
					qm_collect_required_atoms(t, atoms);
					array_for_each(atoms, j, A) {
						if (A == NULL || A->blocker != ATOM_BL_NONE ||
								A->CATEGORY == NULL || A->PN == NULL)
							continue;
						if (!qm_kg_atom_masked(A))
							continue;
						if (best_version(A, BV_INSTALLED) != NULL)
							continue;
						if (qm_kg_plan_satisfies(plan, A))
							continue;
						snprintf(why, sizeof(why), "%s",
								 atom_to_string(A));
						gone = true;
						break;
					}
					array_free(atoms);
					free_set(cuse);
				}
				dep_burn_tree(t);
			}
			atom_implode(ca);
			if (gone) {
				char msg[800];

				warn("qmerge --keep-going: %s dropped because it "
					 "requires %s", ccpn, why);
				snprintf(msg, sizeof(msg), "dropped, requires %s", why);
				qm_kg_record(cpvp, msg);
				add_set(ccpn, qm_kg_mask);
				dropped += qm_plan_drop(plan, ccpn);
				again = true;
			}
		}
	}
	return dropped;
}

/* named targets merged in earlier rounds leave the request so a
 * re-resolve does not do a same-version reinstall of them */
static void
qm_kg_prune_todo(set *todo)
{
	array  *dk;
	size_t  di;
	char   *dcpv;

	if (qm_kg_done == NULL)
		return;
	dk = hash_keys(qm_kg_done);
	array_for_each(dk, di, dcpv) {
		char      ex[560];
		atom_ctx *da;
		char     *dslot = hash_get(qm_kg_done, dcpv);
		array    *tk;
		size_t    ti;
		char     *t;

		snprintf(ex, sizeof(ex), "=%s", dcpv);
		da = atom_explode(ex);
		if (da == NULL)
			continue;
		tk = set_keys(todo);
		array_for_each(tk, ti, t) {
			atom_ctx *ta = atom_explode(t);
			bool      match;

			if (ta == NULL)
				continue;
			match = ta->PN != NULL && da->PN != NULL &&
					strcmp(ta->PN, da->PN) == 0 &&
					(ta->CATEGORY == NULL || da->CATEGORY == NULL ||
					 strcmp(ta->CATEGORY, da->CATEGORY) == 0) &&
					(ta->SLOT == NULL ||
					 (dslot != NULL && *dslot != '\0' &&
					  strcmp(ta->SLOT, dslot) == 0));
			atom_implode(ta);
			if (match) {
				bool ign;

				(void)del_set(t, todo, &ign);
			}
		}
		array_free(tk);
		atom_implode(da);
	}
	array_free(dk);
}

/* one merge round in a forked child, reads the round pipe, attributes
 * the failure, hides the culprit and asks for a re-resolve. 
 * a child killed by a signal is an interrupt of the wohle re-resolve.
 * we got to make sure the authorities know about this. */
static int
qm_kg_round(struct qm_plan *plan, bool *retry)
{
	int    pfd[2];
	pid_t  pid;
	FILE  *rp;
	char   lbuf[768];
	char   curcpv[sizeof(lbuf)]  = "";
	char   curslot[sizeof(lbuf)] = "";
	bool   curopen               = false;
	char   softcpv[sizeof(lbuf)] = "";
	bool   soft = false;
	int    st   = 0;
	int    ec;
	const char *fcpv = NULL;

	*retry = false;
	fflush(NULL);
	if (pipe(pfd) != 0)
		return qm_exec_round(plan);
	pid = fork();
	if (pid < 0) {
		close(pfd[0]);
		close(pfd[1]);
		return qm_exec_round(plan);
	}
	if (pid == 0) {
		close(pfd[0]);
		qm_kg_fd    = pfd[1];
		qm_kg_child = true;
		exit(qm_exec_round(plan));
	}
	close(pfd[1]);
	rp = fdopen(pfd[0], "r");
	if (rp != NULL) {
		while (fgets(lbuf, sizeof(lbuf), rp) != NULL) {
			char  code = lbuf[0];
			char *cpv  = lbuf + 2;
			char *sp;

			if (strlen(lbuf) < 3 || lbuf[1] != ' ')
				continue;
			lbuf[strcspn(lbuf, "\n")] = '\0';
			sp = strchr(cpv, ' ');
			if (sp != NULL)
				*sp++ = '\0';
			switch (code) {
			case 'B':
				snprintf(curcpv, sizeof(curcpv), "%s", cpv);
				snprintf(curslot, sizeof(curslot), "%s",
						 sp != NULL ? sp : "");
				curopen = true;
				break;
			case 'O':
				curopen = false;
				if (qm_kg_done == NULL)
					qm_kg_done = hash_new();
				{
					void *prev = NULL;

					hash_add(qm_kg_done, cpv, xstrdup(curslot), &prev);
					free(prev);
				}
				break;
			case 'S':
				curopen = false;
				snprintf(softcpv, sizeof(softcpv), "%s", cpv);
				soft = true;
				break;
			case 'P':
				qm_kg_record(cpv, "pkg_postinst failed");
				break;
			default:
				break;
			}
		}
		fclose(rp);
	} else {
		close(pfd[0]);
	}
	while (waitpid(pid, &st, 0) < 0 && errno == EINTR)
		;
	if (WIFSIGNALED(st)) {
		warn("qmerge --keep-going: merge interrupted by signal %d, "
			 "not retrying", WTERMSIG(st));
		return EXIT_FAILURE;
	}
	ec = WIFEXITED(st) ? WEXITSTATUS(st) : EXIT_FAILURE;
	if (ec == 0)
		return qm_kg_failed != NULL && array_cnt(qm_kg_failed) > 0
				? EXIT_FAILURE : EXIT_SUCCESS;

	if (soft)
		fcpv = softcpv;
	else if (curopen)
		fcpv = curcpv;
	if (fcpv == NULL || *fcpv == '\0') {
		warn("qmerge --keep-going: round failed before any package "
			 "could be attributed, not retrying");
		return EXIT_FAILURE;
	}
	qm_kg_record(fcpv, soft ? "refused or unfetchable" : "merge failure");
	{
		char      key[700];
		char      ex[560];
		atom_ctx *fa;

		snprintf(ex, sizeof(ex), "=%s", fcpv);
		fa = atom_explode(ex);
		if (fa != NULL && fa->CATEGORY != NULL && fa->PN != NULL) {
			if (strcmp(fcpv, curcpv) == 0 && curslot[0] != '\0')
				snprintf(key, sizeof(key), "%s/%s:%s",
						 fa->CATEGORY, fa->PN, curslot);
			else
				snprintf(key, sizeof(key), "%s/%s",
						 fa->CATEGORY, fa->PN);
			if (qm_kg_mask == NULL)
				qm_kg_mask = create_set();
			if (contains_set(key, qm_kg_mask) != NULL) {
				/* already masked yet planned and failed again: some
				 * selection path bypasses masks (-F does, by design);
				 * retrying would loop forever */
				warn("qmerge --keep-going: %s failed again while "
					 "masked, not retrying", key);
			} else {
				add_set(key, qm_kg_mask);
				warn("qmerge --keep-going: masking %s for this run and "
					 "re-resolving", key);
				*retry = true;
			}
		}
		if (fa != NULL)
			atom_implode(fa);
	}
	return EXIT_FAILURE;
}

/* final failed/dropped report.
 * true when there was anything to report */
static bool
qm_kg_summary(void)
{
	size_t fi;
	char  *fe;

	if (qm_keep_going != 1 || qm_kg_failed == NULL ||
			array_cnt(qm_kg_failed) == 0)
		return false;
	warn("qmerge --keep-going: %zu package(s) failed or were dropped:",
		 array_cnt(qm_kg_failed));
	array_for_each(qm_kg_failed, fi, fe) {
		char *tab = strchr(fe, '\t');

		if (tab != NULL)
			warn("  !!! %.*s (%s)", (int)(tab - fe), fe, tab + 1);
		else
			warn("  !!! %s", fe);
	}
	return true;
}

static int
qm_resolve_and_merge(set *todo)
{
	struct qm_plan plan;
	array         *keys;
	char          *k;
	char          *cpvp;
	size_t         i;

	/* Layer 3 (same-slot unification) round state.Each accepted mask
	 * costs one backtrack round (implcitly some time costs on resolution )
	 * a mask that raises the unsat or conflict count above the round-0 
	 * baseline is reverted, the other side tried once, 
	 * then the pair is given up for the refusal */
	bool   ambig_names = false;
	array *final_dups    = NULL;
	set   *final_planned = NULL;
	int    uni_budget    = qm_slot_unify != 0 ? qm_backtrack : 0;
	int    uni_masks     = 0;
	int    base_unsat    = -1;
	int    base_confl    = -1;
	char   uni_key[560]  = "";
	char   uni_alt[560]  = "";
	char   uni_slot[560] = "";
	bool   uni_alt_tried = false;
	set   *uni_nofix     = create_set();

	if (uni_budget < 0 || uni_budget > QM_MAX_FIXPOINT)
		uni_budget = QM_MAX_FIXPOINT;
	qm_unify_round = 0;

	keys = set_keys(todo);

resolve_again:
	plan.merge    = array_new();
	plan.in_merge = create_set();
	plan.examined = create_set();
	qm_plan_inst  = hash_new();
	qm_demands_free();
	qm_demands    = hash_new();
	qm_unsat_cnt  = 0;
	qm_cur_revdep[0] = '\0';

	/* fresh soft-block auto-unmerge collection for this round */
	if (qm_soft_unmerge != NULL) {
		free_set(qm_soft_unmerge);
		qm_soft_unmerge = NULL;
	}

	array_for_each(keys, i, k) {
		atom_ctx *a = atom_explode(k);
		char     *picked_cat = NULL;

		if (a == NULL)
			continue;
		/* qualify a bare package name the way portage does; the picked
		 * category is our own allocation, atom_implode never frees it */
		if (a->CATEGORY == NULL && a->PN != NULL) {
			bool ambiguous = false;
			set *cands = NULL;

			picked_cat = qm_pick_category(a->PN, &ambiguous, &cands);
			if (picked_cat != NULL) {
				a->CATEGORY = picked_cat;
			} else if (ambiguous) {
				array  *cl = cands != NULL ? set_keys(cands) : NULL;
				size_t  ci;
				char   *cc;

				warn("the short package name '%s' is ambiguous, "
					 "specify one of the following fully-qualified "
					 "names instead:", a->PN);
				if (cl != NULL) {
					array_sort(cl, qm_strcmp_cb);
					array_for_each(cl, ci, cc)
						warn("    %s/%s", cc, a->PN);
					array_free(cl);
				}
				ambig_names = true;
				if (cands != NULL)
					free_set(cands);
				atom_implode(a);
				continue;
			}
			if (cands != NULL)
				free_set(cands);
		}
		qm_forcing_target = qm_force_soft();
		qm_resolve(a, NULL, &plan, 0);
		qm_forcing_target = false;
		atom_implode(a);
		free(picked_cat);
	}

	if (ambig_names) {
		array_free(keys);
		free_set(uni_nofix);
		array_deepfree(plan.merge, free);
		free_set(plan.in_merge);
		free_set(plan.examined);
		qm_plan_inst_free();
		return EXIT_FAILURE;
	}

	/* Layer 2 (backtrack): resolve strands by pulling a newer build of
	 * each wayward binpkg, augmenting plan.merge in place; the sweep below then
	 * reports (and refuses on) whatever couldn't be resolved.
	 * Runs for every resolve like portage's backtrack_depgraph; --backtrack
	 * 0 restores single-shot refuse-on-conflict behavior. */
	if (qm_backtrack != 0 && array_cnt(plan.merge) > 0)
		qm_layer2_resolve(&plan, todo);

	/* Layer 3 (same-slot unification). A run holding two versions of
	 * one cat/pn:slot re-resolves with the losing side masked, like
	 * portage's slot-conflict backtracking. 
	 * QMERGE_SLOT_UNIFY=0 restores the old refuse-on-first-collision behavior. */
	if (uni_budget > 0 && array_cnt(plan.merge) > 0) {
		set   *planned = NULL;
		array *dups    = qm_collect_slot_dups(plan.merge, &planned);
		int    confl   = qm_quiet_conflict_count(plan.merge);
		bool   redo    = false;

		if (base_unsat < 0) {
			base_unsat = qm_unsat_cnt;
			base_confl = confl;
		} else if (uni_key[0] != '\0' &&
				   (qm_unsat_cnt > base_unsat || confl > base_confl)) {
			/* this mask made things worse. it reverts, tries the other side
			 * once, then give the pair up if there's trouble. */
			bool ign;

			(void)del_set(uni_key, qm_unify_mask, &ign);
			if (!uni_alt_tried && uni_alt[0] != '\0') {
				char t[560];

				memcpy(t, uni_key, sizeof(t));
				memcpy(uni_key, uni_alt, sizeof(uni_key));
				memcpy(uni_alt, t, sizeof(uni_alt));
				add_set(uni_key, qm_unify_mask);
				uni_alt_tried = true;
			} else {
				add_set(uni_slot, uni_nofix);
				uni_key[0] = uni_alt[0] = uni_slot[0] = '\0';
				uni_alt_tried = false;
			}
			redo = true;
		} else if (uni_key[0] != '\0') {
			uni_key[0] = uni_alt[0] = uni_slot[0] = '\0';
			uni_alt_tried = false;
		}

		if (!redo && array_cnt(dups) > 0 && uni_masks < uni_budget) {
			size_t di;
			char  *dq;

			array_for_each(dups, di, dq)
				if (qm_unify_arbitrate(dq, planned, todo, uni_nofix,
						uni_key, sizeof(uni_key),
						uni_alt, sizeof(uni_alt),
						uni_slot, sizeof(uni_slot)) == 0) {
					if (qm_unify_mask == NULL)
						qm_unify_mask = create_set();
					add_set(uni_key, qm_unify_mask);
					uni_masks++;
					uni_alt_tried = false;
					redo = true;
					break;
				}
		}

		if (redo) {
			array_deepfree(dups, free);
			free_set(planned);
			qm_verdict_memo_flush();
			qm_use_rejects_flush();
			qm_unify_round++;
			array_deepfree(plan.merge, free);
			free_set(plan.in_merge);
			free_set(plan.examined);
			qm_plan_inst_free();
			goto resolve_again;
		}
		if (array_cnt(dups) > 0) {
			final_dups    = dups;
			final_planned = planned;
		} else {
			array_deepfree(dups, free);
			free_set(planned);
		}
	}
	array_free(keys);
	free_set(uni_nofix);
	if (final_dups != NULL) {
		qm_print_dup_demands(final_dups, final_planned);
		array_deepfree(final_dups, free);
		free_set(final_planned);
	}

	/* keep-going: prune dependents of masked packages before anything
	 * is shown or merged; their provider is gone for this run */
	if (qm_keep_going == 1 && qm_kg_mask != NULL)
		(void)qm_kg_drop_dependents(&plan);

	int rc = EXIT_SUCCESS;

	if (array_cnt(plan.merge) == 0) {
		/* nothing resolved, the request couldn't be satisfied (no candidate
		 * binpkg, or the index/download failed).
		 * Signal failure so the interactive caller skips the "OK to merge"
		 * prompt: there are no packages to offer.
		 * USE-gate rejects explain a respect-use refusal
		 * that would otherwise read as a bare cannot-satisfy. */
		qm_print_use_rejects();
		if (!qm_kg_summary())
			warn("nothing to merge (no candidates could be satisfied)");
		array_deepfree(plan.merge, free);
		free_set(plan.in_merge);
		free_set(plan.examined);
		qm_plan_inst_free();
		return EXIT_FAILURE;
	} else if (pretend) {
		/* pretend: show the resolved merge list (deps first), install status
		 * relative to what is installed, without fetching or merging */
		size_t             n_new = 0, n_up = 0, n_re = 0, n_down = 0;
		unsigned long long dlbytes = 0;
		bool               had_blocks = false;

		qm_blk_reset();
		qm_blk_collect = true;
		(void)qm_quiet_conflict_count(plan.merge);
		qm_blk_collect = false;

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
			bpkg = qm_plan_pick(cpvp, a);
			ba   = a;
			if (bpkg != NULL) {
				/* full atom carries SLOT from metadata, so the status
				 * reflects slot occupancy, matching emerge and the
				 * slot-collapse install path */
				atom_ctx *bat = tree_pkg_atom(bpkg, true);

				st = qm_slot_status(bat, NULL);
				/* cosmetic: show the binpkg-multi-instance build id like
				 * emerge's -N.
				 * Purely display, the [R]/[U] decision above
				 * is version-only and ignores the build id. */
				if (bat->BUILDID > 0)
					snprintf(bidbuf, sizeof(bidbuf), "-%u", bat->BUILDID);
			}
			(void)ba;
			(void)inst;
			/* colored via the global rule: tty auto-color, disabled by
			 * -C/--nocolor/NOCOLOR/NO_COLOR/QMERGE_NOCOLOR, forced by
			 * --color (the color globals are empty strings when nocolor
			 * wins).
			 * Binary merges use portage's PKG_BINARY_MERGE
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
				default:            break;
			}
			if (bpkg != NULL &&
					faccessat(tree_pkg_get_portroot_fd(bpkg),
							  tree_pkg_get_path(bpkg), R_OK, 0) != 0) {
				char *szs = tree_pkg_meta(bpkg, Q_SIZE);

				if (szs != NULL && *szs != '\0')
					dlbytes += strtoull(szs, NULL, 10);
			}
			/* well, since qmerge is always -g, we gotta show it
			 * as well. portage always does. */
			{
				const char *grn = bpkg != NULL ?
						qm_repo_name_of_pkg(bpkg) : NULL;
				bool        isg = bpkg != NULL &&
						(grn == NULL || grn[0] != '@');

				printf("[%sbinary%s %s%s%s%s%s%s", pc, NORM,
					   stc, st, NORM,
					   isg && *NORM != '\0' ? "\033[35;01m" : "",
					   isg ? "g" : "",
					   isg ? NORM : "");
			}
				if (bpkg != NULL) {
					const char *km = qm_keyword_marker(bpkg);

					if (km[0] != '\0')
						printf(" %s%s%s",
							   *NORM == '\0' ? "" : "\033[33;01m",
							   km, NORM);
				}
				/* merge-list entries may carry a ::binrepo pin; the [repo]
				 * tag already shows it, keep the name clean */
				{
					const char *rsep = strstr(cpvp, "::");
					int         cl   = rsep != NULL ?
							(int)(rsep - cpvp) : (int)strlen(cpvp);

					printf("] %s%.*s%s%s", pc, cl, cpvp, bidbuf, NORM);
				}

				/* SLOT/SUBSLOT and source-repo provenance, like emerge's
				 * cat/pf-BID:slot/sub::repo.
				 * Portage colors the whole atom (name+slot+repo) as one run 
				 * via pkgprint, so reuse the package color pc 
				 * rather than highlighting slot/repo apart. */
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
			if (qm_user_verbose && bpkg != NULL)
				qm_print_use_verbose(bpkg);
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
			/* if -v (yes, verbose) then name the dep edges that pulled this entry into the
			 * merge list, from the resolver's demand list */
			if (qm_user_verbose && bpkg != NULL && qm_demands != NULL) {
				atom_ctx *bat = tree_pkg_atom(bpkg, true);
				char      dslot[512];
				array    *dl;

				snprintf(dslot, sizeof(dslot), "%s/%s:%s",
						 bat->CATEGORY ? : "", bat->PN ? : "",
						 bat->SLOT ? : "");
				dl = hash_get(qm_demands, dslot);
				if (dl != NULL && array_cnt(dl) > 0) {
					set    *seen  = create_set();
					size_t  di;
					char   *rec;
					size_t  shown = 0;

					printf("           %spulled in by:%s", DKBLUE, NORM);
					array_for_each(dl, di, rec) {
						char  buf[560];
						char *sep;

						snprintf(buf, sizeof(buf), "%s", rec);
						sep = strchr(buf, '\1');
						if (sep != NULL)
							*sep = '\0';
						if (contains_set(buf, seen) != NULL)
							continue;
						add_set(buf, seen);
						shown++;
						if (shown > 3)
							continue;
						printf(" %s", buf);
						if (sep != NULL && sep[1] != '\0')
							printf(" (%s)", sep + 1);
					}
					if (shown > 3)
						printf(" and %zu more", shown - 3);
					printf("\n");
					free_set(seen);
				}
			}
			atom_implode(a);
		}
		had_blocks = qm_print_blocks();
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

			{
				char dlbuf[40];

				qm_fmt_kib(dlbuf, sizeof(dlbuf), dlbytes);
				printf("\nTotal: %zu package%s%s%s%s, "
					   "Size of downloads: %s KiB\n",
					   array_cnt(plan.merge),
					   array_cnt(plan.merge) == 1 ? "" : "s",
					   po ? " (" : "", parts, po ? ")" : "",
					   dlbuf);
			}
		}
		qm_print_use_rejects();
		if (!qm_soname_sweep(plan.merge))
			rc = EXIT_FAILURE;
		/* surface subslot conflicts in the merge list too, like emerge does; a
		 * contradictory resolution is a failure even in pretend, and (crucially)
		 * makes the interactive dry-run return non-zero so the caller skips
		 * the "OK to merge" prompt instead of offering a merge list we refuse. */
		if (qm_check_slot_conflicts(plan.merge, NULL, NULL) > 0 &&
			!qm_ignore_slot_conflicts()) {
			rc = EXIT_FAILURE;
			if (had_blocks) {
				printf("\n * Error: The above package list contains "
					   "packages which cannot be\n * installed at the "
					   "same time on the same system.\n");
				warn("unmerge the blocked packages yourself, set "
					 "QMERGE_BLOCKERS to auto-unmerge soft blocks, or "
					 "QMERGE_IGNORE_SLOT_CONFLICTS to override");
			}
		}
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
	} else if (qm_blk_sweep(plan.merge) > 0 &&
			   !qm_ignore_slot_conflicts()) {
		/* the resolution would strand installed packages we can't rebuild from a
		 * binpkg; bail instead of half-migrating and breaking the system */
		if (qm_print_blocks())
			printf("\n * Error: The above package list contains "
				   "packages which cannot be\n * installed at the "
				   "same time on the same system.\n");
		warn("refusing to merge: the plan would break installed packages "
			 "(subslot conflict above). Rebuild them from source with "
			 "emerge, or set QMERGE_IGNORE_SLOT_CONFLICTS=1 to force it.");
		rc = EXIT_FAILURE;
	} else if (!qm_soname_sweep(plan.merge)) {
		warn("refusing to merge: unresolved soname dependencies above "
			 "(QMERGE_SONAME_DEPS=hold)");
		rc = EXIT_FAILURE;
	} else {
		bool kg_retry = false;

		if (qm_keep_going == 1 && !fetch_only)
			rc = qm_kg_round(&plan, &kg_retry);
		else
			rc = qm_exec_round(&plan);

		if (kg_retry && ++qm_kg_rounds <= QM_MAX_FIXPOINT) {
			/* round state teardown, exactly the Layer-3 redo dance */
			qm_verdict_memo_flush();
			qm_use_rejects_flush();
			array_deepfree(plan.merge, free);
			free_set(plan.in_merge);
			free_set(plan.examined);
			qm_plan_inst_free();
			final_dups    = NULL;
			final_planned = NULL;
			/* the round child changed the VDB on disk; the resolver
			 * cache predates it */
			if (qmerge_vdb_tree != NULL) {
				tree_close(qmerge_vdb_tree);
				qmerge_vdb_tree = NULL;
			}
			qm_kg_prune_todo(todo);
			keys      = set_keys(todo);
			uni_nofix = create_set();
			goto resolve_again;
		}
		if (kg_retry)
			warn("qmerge --keep-going: giving up after %d rounds",
				 QM_MAX_FIXPOINT);
	}

	array_deepfree(plan.merge, free);
	free_set(plan.in_merge);
	free_set(plan.examined);
	qm_plan_inst_free();


	/* this is where we show that the config files are needing update*/
	if (qm_cfg_pending > 0 && !pretend) {
		char   dirs[1024] = "";
		size_t off = 0;
		size_t n;
		char  *d;
		array *dk = set_keys(qm_cfg_dirs);

		array_for_each(dk, n, d)
			off += (size_t)snprintf(dirs + off,
					off < sizeof(dirs) ? sizeof(dirs) - off : 0,
					"%s'%s'", off ? ", " : "", d);
		array_free(dk);
		printf("\n %s*%s IMPORTANT: %zu config file%s in %s need%s "
			   "updating.\n", YELLOW, NORM,
			   qm_cfg_pending, qm_cfg_pending == 1 ? "" : "s", dirs,
			   qm_cfg_pending == 1 ? "s" : "");
		printf(" %s*%s Use etc-update or dispatch-conf to merge them.\n",
			   YELLOW, NORM);
	}
	qm_cfg_pending = 0;
	if (qm_cfg_dirs != NULL) {
		free_set(qm_cfg_dirs);
		qm_cfg_dirs = NULL;
	}

	/* GLEP 42: surface any unread news, like portage's post-emerge notice */
	qm_news_notice();

	if (qm_kg_summary())
		rc = EXIT_FAILURE;

	return rc;
}

/* Faithful port of Portage's vardbapi.get_counter_tick_core()
 * (lib/portage/dbapi/vartree.py): return a COUNTER value that is at
 * least one greater than both the global counter file and the highest
 * COUNTER of any installed package.
 * Trusting only the global file can yield a value that is too low 
 * (e.g. after a restore), which corrupts slot ordering and 
 * AUTOCLEAN because a freshly merged package would carry a lower 
 * COUNTER than the version it replaces. */
static int  qm_vdb_lockfd = -1;
static char qm_vdb_lockp[2 * _Q_PATH_MAX + 64];

static int
qm_vdb_lock(void)
{
	if (qm_vdb_lockfd < 0) {
		char         vdbroot[_Q_PATH_MAX];
		char        *slash;
		int          fd;
		struct flock fl;

		snprintf(vdbroot, sizeof(vdbroot), "%s%s", portroot, portvdb);
		{
			size_t vl = strlen(vdbroot);
			while (vl > 1 && vdbroot[vl - 1] == '/')
				vdbroot[--vl] = '\0';
		}
		slash = strrchr(vdbroot, '/');
		if (slash != NULL) {
			*slash = '\0';
			snprintf(qm_vdb_lockp, sizeof(qm_vdb_lockp),
					"%s/.%s.portage_lockfile", vdbroot, slash + 1);
		} else {
			snprintf(qm_vdb_lockp, sizeof(qm_vdb_lockp),
					".%s.portage_lockfile", vdbroot);
		}

		fd = open(qm_vdb_lockp, O_CREAT | O_RDWR | O_CLOEXEC, 0660);
		if (fd < 0) {
			warnp("cannot open %s", qm_vdb_lockp);
			return -1;
		}

		memset(&fl, 0, sizeof(fl));
		fl.l_type   = F_WRLCK;
		fl.l_whence = SEEK_SET;
		if (fcntl(fd, F_SETLK, &fl) != 0) {
			if (errno != EACCES && errno != EAGAIN) {
				warnp("cannot lock %s", qm_vdb_lockp);
				close(fd);
				return -1;
			}
			warn("waiting for vdb lock %s", qm_vdb_lockp);
			while (fcntl(fd, F_SETLKW, &fl) != 0) {
				if (errno == EINTR)
					continue;
				warnp("cannot lock %s", qm_vdb_lockp);
				close(fd);
				return -1;
			}
		}
		qm_vdb_lockfd = fd;
	}
	return qm_vdb_lockfd;
}

static void
qm_vdb_unlock(void)
{
	if (qm_vdb_lockfd < 0)
		return;
	close(qm_vdb_lockfd);
	qm_vdb_lockfd = -1;
}

static long
qm_get_counter_tick_core(void)
{
	char           path[_Q_PATH_MAX];
	char          *buf = NULL;
	size_t         buf_len = 0;
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
 * next install sees a strictly greater value.
 * Returns the new counter. */
static long
qm_counter_tick(void)
{
	char  path[_Q_PATH_MAX];
	char  tmp[_Q_PATH_MAX];
	long  counter;
	FILE *fp;
	int   dir_len;
	int   lk;

	lk = qm_vdb_lock();
	counter = qm_get_counter_tick_core();

	dir_len = snprintf(path, sizeof(path), "%s%s", portroot, portedb);
	mkdir_p(path, 0755);
	snprintf(path + dir_len, sizeof(path) - dir_len, "/counter");
	snprintf(tmp, sizeof(tmp), "%.*s/counter.qmerge",
			 (int)MIN((size_t)dir_len, sizeof(tmp) - 16), path);
	if ((fp = fopen(tmp, "w")) != NULL) {
		bool ok = fprintf(fp, "%ld", counter) >= 0;
		if (fclose(fp) != 0)
			ok = false;
		if (!ok || rename(tmp, path) != 0) {
			warn("failed to update global counter %s", path);
			unlink(tmp);
		}
	} else {
		warn("failed to write global counter %s", tmp);
	}

	if (lk >= 0)
		qm_vdb_unlock();

	return counter;
}

/* GLEP 78/63/79 signature posture for a package served by binrepo ri
 * (-1 unknown), FEATURES and binrepos.conf combined with portage's
 * precedence (lib/portage/gpkg.py:793-822):
 *   verify  = check signatures when present (default on)
 *   request = signatures are mandatory (missing sig -> refuse)
 * binpkg-ignore-signature prio over binpkg-request-signature which has prio over the
 * per-repo verify-signature overrides the verify-if-present
 * default. A global request can NOT be relaxed per repo. */
static void
qm_sig_effective(ssize_t ri, bool *request, bool *verify, const char **why)
{
	bool ign = contains_set("binpkg-ignore-signature", features) != NULL;
	bool req = contains_set("binpkg-request-signature", features) != NULL;
	int  vs  = -1;

	if (ri >= 0 && (size_t)ri < qm_nbinrepos)
		vs = qm_binrepos[ri].verify_sig;

	*why = "binpkg-request-signature";
	if (ign) {
		*request = false;
		*verify  = false;
	} else if (req) {
		*request = true;
		*verify  = true;
	} else if (vs == 1) {
		*request = true;
		*verify  = true;
		*why     = "binrepos.conf verify-signature=true";
	} else if (vs == 0) {
		*request = false;
		*verify  = false;
	} else {
		*request = false;
		*verify  = true;
	}
}

/* Portage's PORTAGE_TRUST_HELPER equivalent (bintree.py:_run_trust_helper):
 * before a run that will verify signatures, refresh the binpkg trust keyring
 * so gpgme has trusted keys to check against.
 * Runs only when signatures are mandatory (binpkg-request-signature, 
 * or a repo with verify-signature=true), we will actually merge 
 * (not pretend, not fetch-only) and we are root.
 * QMERGE_TRUST_HELPER selects the helper: unset = the built-in qetuto applet,
 * "false"/"no"/"0"/"" disables it (escape hatch), anything else is run via
 * the shell as an external command (point it at /usr/bin/getuto to defer to
 * app-portage/getuto).
 * qetuto self-throttles to once/day via .getuto.last,
 * so the common warm-cache cost is a single stat(). */
static void
qm_run_trust_helper(void)
{
	const char *th;
	pid_t       pid;
	int         st;

	if (pretend || fetch_only || geteuid() != 0)
		return;
	if (!qm_sigs_mandatory())
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

			av[n++] = q_deconst("qetuto");
			if (verbose > 0)
				av[n++] = q_deconst("-v");
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

/* the keyring home used for signature verification */
static const char *
qm_gpg_home(void)
{
	if (binpkg_gpg_verify_gpg_home != NULL &&
			binpkg_gpg_verify_gpg_home[0] != '\0')
		return binpkg_gpg_verify_gpg_home;
	return QM_GPG_HOME;
}

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
	gpgme_ctx_set_engine_info(ctx, GPGME_PROTOCOL_OpenPGP, NULL, qm_gpg_home());

	if (gpgme_op_verify(ctx, sig, signed_data, plain) == GPG_ERR_NO_ERROR) {
		vr = gpgme_op_verify_result(ctx);
		/* accept if ANY signature is good+trusted+valid and additionally reject
		 * one whose key is locally disabled/revoked/expired even if gpg
		 * summarised it VALID (defense-in-depth) */
		for (s = (vr != NULL ? vr->signatures : NULL); s != NULL; s = s->next) {
			gpgme_key_t key = NULL;

			if (s->status != GPG_ERR_NO_ERROR ||
					!(s->summary & GPGME_SIGSUM_VALID))
				continue;
			if (s->fpr != NULL &&
					gpgme_get_key(ctx, s->fpr, &key, 0) == GPG_ERR_NO_ERROR &&
					key != NULL) {
				bool bad = key->disabled || key->revoked || key->expired;
				gpgme_key_release(key);
				if (bad)
					continue;
			}
			ok = true;
			break;
		}
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
 * STREAMING (no extract to disk, no whole-member buffering).
 * The container structure and every member's checksum-against-Manifest are already
 * validated by qm_gpkg_check(); here we only establish trust:
 *   1. the Manifest must carry a good, trusted cleartext signature
 *   2. every signed member (all but gpkg-1) must have a detached .sig that
 *      verifies against its data
 * The signed Manifest plus the (already verified) checksum chain
 * authenticate the members; the detached sigs are portage's additional
 * belt-and-braces.
 * Returns true iff the package is trustworthy.
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
	gid_t pwgid = (gid_t)-1;
	uid_t uid   = qm_passwd_uid("nobody", &pwgid);
	gid_t gid   = qm_group_gid("nogroup");

	if (gid == (gid_t)-1)
		gid = pwgid != (gid_t)-1 ? pwgid : (gid_t)65534;
	if (uid == (uid_t)-1)
		uid = (uid_t)65534;

	/* groups, then gid, then uid, can't reorder, uid drop is one-way.
	 * best-effort: a failed drop just verifies at the current privilege */
	/* keep going on failure; supplementary groups are the least of it */
	if (setgroups(0, NULL) != 0)
		{ }
	if (setgid(gid) != 0)
		warn("could not drop gid for signature verification");
	if (setuid(uid) != 0)
		warn("could not drop to nobody for signature verification");
}

/* Verify a signed gpkg with privileges dropped: when root, fork a child
 * that becomes nobody and runs the gpgme verification, and take its exit
 * status as the verdict.
 * A fork failure falls back to verifying in-process (no worse than before).
 * Returns true iff trustworthy. */
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
		/* fork died; do it here */
		return qm_gpkg_verify_impl(gpkg_path);

	while (waitpid(pid, &status, 0) < 0 && errno == EINTR)
		;
	return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

/* streaming read callback pulling the current gpkg member's data */
static size_t
qm_archive_read_cb(char *dest, size_t destlen, void *ctx)
{
	la_ssize_t n = archive_read_data((struct archive *)ctx, dest, destlen);
	return n < 0 ? (size_t)-1 : (size_t)n;
}

/* GLEP 78 container hardening + Manifest checksum verification, run on
 * EVERY gpkg (signed or not) before decompression, matching portage's
 * _verify_binpkg (lib/portage/gpkg.py).
 * Members are hashed by streaming (no extract to disk), so large 
 * packages are not buffered.
 * Checks:
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
	int                   ar       = ARCHIVE_EOF;
	size_t                i;
	struct gpkg_member   *m;

	a = archive_read_new();
	archive_read_support_format_all(a);
	archive_read_support_filter_all(a);
	if (archive_read_open_filename(a, gpkg_path, BUFSIZ) != ARCHIVE_OK) {
		archive_read_free(a);
		free_set(seen);
		array_free(members);
		return false;
	}

	while (ok && (ar = archive_read_next_header(a, &e)) == ARCHIVE_OK) {
		const char *name = archive_entry_pathname(e);
		const char *base;

		if (!gpkg_member_ok(name, archive_entry_filetype(e) == AE_IFREG,
				&prefix, seen, gpkg_path)) {
			ok = false; break;
		}

		base = strchr(name, '/') + 1;
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
			if (hash_multiple_cb(qm_archive_read_cb, a, NULL, NULL, NULL,
					m->sha512, m->blake2b, &flen,
					HASH_SHA512 | HASH_BLAKE2B) != 0) {
				warn("%s: read error hashing member %s", gpkg_path, base);
				ok = false;
			}
			m->size = (long long)flen;
		}
		array_append(members, m);
	}
	if (ok && ar != ARCHIVE_EOF) {
		warn("%s: malformed or truncated archive: %s",
				gpkg_path, archive_error_string(a));
		ok = false;
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
	if (ok)
		ok = gpkg_manifest_verify(manifest, members, gpkg_path);

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
/* ENABLE_GPKG
 * Probably this is a recommendation to the user
 * or ... the reader, because this is done slightly above. */
#endif

/* Old: oh shit getting into pkg mgt here. FIXME: write a real dep resolver.
 * New: but this is no longer the issue. We finally wrote one. */
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


/* portage collision-protect/protect-owned engine (vartree.py
 * _collision_protect): refuse to overwrite files on disk that the
 * incoming package does not own.
 * Detection is cheap (one lstat per image file, CONTENTS of the 
 * replaced slot members only); the full VDB owner sweep runs 
 * only when something actually collided. */
struct qm_colstate {
	set    *self;
	array  *cols;
	array  *symcols;
	size_t  eprefix_len;
	int     ig_argc;
	char  **ig_argv;
	int     cp_argc;
	char  **cp_argv;
	int     cpm_argc;
	char  **cpm_argv;
};
static struct qm_colstate qm_cols;

static int
qm_collision_scan_cb(const char *fpath, const struct stat *sb,
                     int typeflag, struct FTW *ftwbuf)
{
	const char  *cpath = fpath + sizeof("image") - 1;
	char         dest[_Q_PATH_MAX * 2];
	struct stat  dst;
	int          i;

	(void)sb;
	(void)ftwbuf;

	if (typeflag != FTW_F && typeflag != FTW_SL)
		return 0;
	if (*cpath == '\0')
		return 0;

	snprintf(dest, sizeof(dest), "%s%s", portroot, cpath);
	if (lstat(dest, &dst) != 0)
		return 0;

	if (typeflag == FTW_SL && S_ISDIR(dst.st_mode)) {
		array_append_strcpy(qm_cols.symcols, cpath);
		array_append_strcpy(qm_cols.cols, cpath);
		return 0;
	}

	if (contains_set(cpath, qm_cols.self) != NULL)
		return 0;
	if (config_protected(cpath + qm_cols.eprefix_len,
				qm_cols.cp_argc, qm_cols.cp_argv,
				qm_cols.cpm_argc, qm_cols.cpm_argv))
		return 0;

	for (i = 1; i < qm_cols.ig_argc; i++) {
		const char *pat = qm_cols.ig_argv[i];

		if (fnmatch(pat, cpath + qm_cols.eprefix_len, 0) == 0)
			return 0;
		if (strpbrk(pat, "*?[") == NULL) {
			char dpat[_Q_PATH_MAX];

			snprintf(dpat, sizeof(dpat), "%s/*", pat);
			if (fnmatch(dpat, cpath + qm_cols.eprefix_len, 0) == 0)
				return 0;
		}
	}

	array_append_strcpy(qm_cols.cols, cpath);
	return 0;
}

struct qm_colown {
	set   *want;
	array *skip;
	bool   owned_any;
};

static int
qm_collision_owner_cb(tree_pkg_ctx *pkg_ctx, void *priv)
{
	struct qm_colown *co = priv;
	atom_ctx         *a  = tree_pkg_atom(pkg_ctx, false);
	char             *contents;
	char             *line;
	char             *savep;
	bool              first = true;
	size_t            n;
	tree_pkg_ctx     *m;

	if (a == NULL || a->CATEGORY == NULL || a->PF == NULL)
		return 0;
	if (co->skip != NULL) {
		array_for_each(co->skip, n, m) {
			atom_ctx *ma = tree_pkg_atom(m, false);

			if (ma != NULL &&
					strcmp(ma->CATEGORY, a->CATEGORY) == 0 &&
					strcmp(ma->PF, a->PF) == 0)
				return 0;
		}
	}

	contents = tree_pkg_meta(pkg_ctx, Q_CONTENTS);
	if (contents == NULL)
		return 0;
	contents = xstrdup(contents);

	for (line = strtok_r(contents, "\n", &savep);
			line != NULL;
			line = strtok_r(NULL, "\n", &savep))
	{
		contents_entry *e = contents_parse_line(line);

		if (e == NULL || contains_set(e->name, co->want) == NULL)
			continue;
		if (first) {
			warn("  %s owns:", atom_format("%[CAT]%[PF]", a));
			first = false;
		}
		warn("    %s", e->name);
		co->owned_any = true;
	}

	free(contents);
	return 0;
}

/* returns only when the merge may proceed, aborts via err() otherwise */
static void
qm_collision_protect(atom_ctx *matom, array *slotmembers,
                     size_t eprefix_len,
                     int cp_argc, char **cp_argv,
                     int cpm_argc, char **cpm_argv)
{
	bool          cprot  = contains_set("collision-protect", features) != NULL;
	bool          powned = contains_set("protect-owned", features) != NULL;
	bool          owned  = false;
	size_t        n;
	char         *p;
	tree_pkg_ctx *m;

	qm_cols.self        = create_set();
	qm_cols.cols        = array_new();
	qm_cols.symcols     = array_new();
	qm_cols.eprefix_len = eprefix_len;
	qm_cols.cp_argc     = cp_argc;
	qm_cols.cp_argv     = cp_argv;
	qm_cols.cpm_argc    = cpm_argc;
	qm_cols.cpm_argv    = cpm_argv;
	makeargv(collision_ignore, &qm_cols.ig_argc, &qm_cols.ig_argv);

	if (slotmembers != NULL) {
		array_for_each(slotmembers, n, m) {
			char *cts = tree_pkg_meta(m, Q_CONTENTS);
			char *line;
			char *savep;

			if (cts == NULL)
				continue;
			cts = xstrdup(cts);
			for (line = strtok_r(cts, "\n", &savep);
					line != NULL;
					line = strtok_r(NULL, "\n", &savep))
			{
				contents_entry *e = contents_parse_line(line);

				if (e != NULL)
					add_set(e->name, qm_cols.self);
			}
			free(cts);
		}
	}

	nftw("image", qm_collision_scan_cb, 64, FTW_PHYS);

	freeargv(qm_cols.ig_argc, qm_cols.ig_argv);
	free_set(qm_cols.self);

	if (array_cnt(qm_cols.cols) > 0) {
		warn("this package would overwrite one or more files that may "
			 "belong to other packages (see list below)");
		warn("detected file collision(s):");
		array_for_each(qm_cols.cols, n, p)
			warn("  %s", p);

		if (cprot || powned || array_cnt(qm_cols.symcols) > 0) {
			struct qm_colown  co;
			tree_ctx         *vdb;

			warn("searching all installed packages for file collisions...");
			co.want      = create_set();
			co.skip      = slotmembers;
			co.owned_any = false;
			array_for_each(qm_cols.cols, n, p)
				add_set(p, co.want);
			vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);
			if (vdb != NULL) {
				tree_foreach_pkg_fast(vdb, qm_collision_owner_cb, &co, NULL);
				tree_close(vdb);
			}
			free_set(co.want);
			if (!co.owned_any)
				warn("none of the installed packages claim the file(s)");
			owned = co.owned_any;
		}
	}

	if (array_cnt(qm_cols.symcols) > 0)
		err("package %s NOT merged: collisions between symlinks and "
			"directories are forbidden by PMS section 13.4",
			atom_format("%[CAT]%[PF]", matom));
	if (array_cnt(qm_cols.cols) > 0) {
		if (cprot)
			err("package %s NOT merged due to file collisions "
				"(FEATURES=collision-protect)",
				atom_format("%[CAT]%[PF]", matom));
		else if (powned && owned)
			err("package %s NOT merged due to file collisions "
				"(FEATURES=protect-owned)",
				atom_format("%[CAT]%[PF]", matom));
		else
			warn("package %s merged despite file collisions",
				 atom_format("%[CAT]%[PF]", matom));
	}

	array_deepfree(qm_cols.cols, NULL);
	array_deepfree(qm_cols.symcols, NULL);
}


/* we need some explanations here for each of the elements bellow,
 * this is probably some of the most important stuff here,
 * since pkg_merge is a ship icebreaker in our functions, basically */
static void
pkg_merge(int level, const depend_atom *qatom, tree_pkg_ctx *mpkg)
{
	set            *objs;
	tree_pkg_ctx   *previnst;
	array          *slotmembers = NULL;
	array          *pres_paths  = NULL;
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
	 * pass above has fetched the dependencies as well */
	if (fetch_only)
		return;

	if (pretend == 100) {
		return;
	}

	/* create directories in the vdb repo if non-pretend mode, 
	 * of course */
	if (!pretend)
	{
		snprintf(buf, sizeof(buf), "%s/%s/%s",
				 portroot, portvdb, matom->CATEGORY);
		if (mkdir_p(buf, 0755) != 0)
			errp("cannot create VDB directory %s", buf);
	}

	snprintf(buf, sizeof(buf), "%s%s/qmerge/%s/%s",
			 portroot, port_tmpdir, matom->CATEGORY, matom->PF);
	if (mkdir_p(buf, 0755) != 0)
		errp("cannot create work directory %s", buf);
	xchdir(buf);
	xasprintf(&D, "%s/image", buf);
	xasprintf(&T, "%s/temp", buf);

	/* Doesn't actually remove $PWD, just everything under it.
	 * but this is slightly dangerous, we'll have to do some verifications
	 * here before doing it. */
	rm_rf(".");

	mkdir("temp", 0755);
	mkdir("vdb", 0755);
	mkdir("image", 0755);

	p = tree_pkg_get_path(mpkg);
	/* p is portroot-relative and cwd is the build tempdir here */
	snprintf(buf, sizeof(buf), "%s/%s", portroot, p);

	/* xpak cannot carry a GLEP 78 signature at all */
	{
		bool        breq, bver;
		const char *bwhy;

		qm_sig_effective(qm_repoidx_of_pkg(mpkg), &breq, &bver, &bwhy);
		if (breq && !qm_binpkg_is_gpkg(buf))
			err("%s is an xpak package and cannot carry an OpenPGP "
				"signature, but %s is enabled; refusing to merge",
				atom_format("%[CAT]%[PF]", matom), bwhy);
	}

	if (qm_binpkg_is_gpkg(buf))
	{
#ifdef ENABLE_GPKG
		/* unpack the whole thing to temp, dropping the pkg name dir, so
		 * we end up with generic files in temp */
		struct archive       *a;
		struct archive       *t;
		struct archive_entry *entry;

		snprintf(buf, sizeof(buf), "%s/%s", portroot, p);

		/* GLEP 78/63/79: verify signatures BEFORE decompressing anything.
		 * Portage never extracts a package whose signature is required but
		 * missing/invalid (gpkg.py verifies ahead of extractall). */
		{
			bool        sig_request, sig_verify;
			bool        sig_present;
			const char *sig_why;

			/* per-repo verify-signature take less precedence over
			 * portage's FEATURES, so we comply*/
			qm_sig_effective(qm_repoidx_of_pkg(mpkg),
							 &sig_request, &sig_verify, &sig_why);
			sig_present = qm_gpkg_is_signed(buf);

#ifndef HAVE_GPGME
			/* built without gpgme: we can see whether a signature is
			 * present but cannot verify it.
			 * Don't pretend to enforce, refuse only when signatures 
			 * are mandatory, otherwise install unverified 
			 * (same posture as binpkg-ignore-signature). */
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
		int ar;
		a = archive_read_new();
		t = archive_write_disk_new();
		archive_read_support_format_all(a);
		if (archive_read_open_filename(a, buf, BUFSIZ) != ARCHIVE_OK)
			err("failed to open %s: %s", buf, archive_error_string(a));
		while ((ar = archive_read_next_header(a, &entry)) == ARCHIVE_OK) {
			const char *fname = archive_entry_pathname(entry);
			size_t      size;
			la_int64_t  off;

			fname = strchr(fname, '/');
			if (fname == NULL)
				continue;
			fname++;
			if (*fname == '\0')
				/* bug #968185 */
				continue;

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
			fname = archive_entry_pathname(entry);

			if (archive_write_header(t, entry) != ARCHIVE_OK)
				err("failed to unpack from gpkg '%s': %s",
					fname, archive_error_string(t));
			while ((ar = archive_read_data_block(a, (const void **)&p,
										   &size, &off)) == ARCHIVE_OK)
			{
				if (archive_write_data_block(t, p, size, off) != ARCHIVE_OK)
					err("failed to write from gpkg '%s': %s\n",
						fname, archive_error_string(t));
			}
			if (ar != ARCHIVE_EOF)
				err("failed reading gpkg member '%s': %s",
					fname, archive_error_string(a));
			archive_write_finish_entry(t);
		}
		if (ar != ARCHIVE_EOF)
			err("failed reading gpkg archive: %s",
				archive_error_string(a));
		archive_read_close(a);
		archive_read_free(a);
		if (archive_write_close(t) < ARCHIVE_WARN)
			err("failed to finalize gpkg extraction: %s",
				archive_error_string(t));
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
									   	   ARCHIVE_EXTRACT_XATTR |
									   	   ARCHIVE_EXTRACT_SECURE_SYMLINKS |
									   	   ARCHIVE_EXTRACT_SECURE_NODOTDOT |
									   	   ARCHIVE_EXTRACT_SECURE_NOABSOLUTEPATHS));
		if (archive_read_open_filename(a, "../temp/metadata",
									   BUFSIZ) != ARCHIVE_OK)
			err("failed to open metadata: %s", archive_error_string(a));
		while ((ar = archive_read_next_header(a, &entry)) == ARCHIVE_OK) {
			const char *fname = archive_entry_pathname(entry);
			size_t      size;
			la_int64_t  off;

			fname = strchr(fname, '/');
			if (fname == NULL)
				continue;
			fname++;
			if (*fname == '\0')
				/* bug #968185 */
				continue;

			archive_entry_set_pathname(entry, fname);
			fname = archive_entry_pathname(entry);

			if (archive_write_header(t, entry) != ARCHIVE_OK)
				err("failed to unpack metadata '%s': %s",
					fname, archive_error_string(t));
			while ((ar = archive_read_data_block(a, (const void **)&p,
										   &size, &off)) == ARCHIVE_OK)
			{
				if (archive_write_data_block(t, p, size, off) != ARCHIVE_OK)
					err("failed to write metadata '%s': %s\n",
						fname, archive_error_string(t));
			}
			if (ar != ARCHIVE_EOF)
				err("failed reading gpkg member '%s': %s",
					fname, archive_error_string(a));
			archive_write_finish_entry(t);
		}
		if (ar != ARCHIVE_EOF)
			err("failed reading gpkg archive: %s",
				archive_error_string(a));
		archive_read_close(a);
		archive_read_free(a);
		if (archive_write_close(t) < ARCHIVE_WARN)
			err("failed to finalize gpkg extraction: %s",
				archive_error_string(t));
		archive_write_free(t);
		xchdir("..");

		/* finally the package image. */
		xchdir("image");
		a = archive_read_new();
		t = archive_write_disk_new();
		archive_read_support_format_all(a);
		archive_read_support_filter_all(a);
		archive_write_disk_set_options(t, (ARCHIVE_EXTRACT_PERM |
									   	   ARCHIVE_EXTRACT_TIME |
									   	   ARCHIVE_EXTRACT_ACL |
									   	   ARCHIVE_EXTRACT_FFLAGS |
									   	   ARCHIVE_EXTRACT_XATTR |
									   	   ARCHIVE_EXTRACT_SECURE_SYMLINKS |
									   	   ARCHIVE_EXTRACT_SECURE_NODOTDOT |
									   	   ARCHIVE_EXTRACT_SECURE_NOABSOLUTEPATHS));
		if (archive_read_open_filename(a, "../temp/image",
									   BUFSIZ) != ARCHIVE_OK)
			err("failed to open metadata: %s", archive_error_string(a));
		while ((ar = archive_read_next_header(a, &entry)) == ARCHIVE_OK) {
			const char *fname = archive_entry_pathname(entry);
			size_t      size;
			la_int64_t  off;

			fname = strchr(fname, '/');
			if (fname == NULL)
				continue;
			fname++;
			if (*fname == '\0')
				/* bug #968185 */
				continue;

			archive_entry_set_pathname(entry, fname);
			fname = archive_entry_pathname(entry);

			/* handle hardlinks offset, #968291 */
#ifdef HAVE_ARCHIVE_ENTRY_HARDLINK_IS_SET
			if (archive_entry_hardlink_is_set(entry))
#else
			if (archive_entry_hardlink(entry) != NULL)
#endif
			{
				const char *hlinktrg = archive_entry_hardlink(entry);
				hlinktrg = strchr(hlinktrg, '/');
				if (hlinktrg == NULL ||
					hlinktrg[1] == '\0')
				/* really, how? */
				{
					warn("%s has invalid hardlink target '%s', skipping",
						 fname, archive_entry_hardlink(entry));
					continue;
				}
				archive_entry_set_hardlink(entry, &hlinktrg[1]);
			}

			if (archive_write_header(t, entry) != ARCHIVE_OK)
				err("failed to unpack image '%s': %s",
					fname, archive_error_string(t));
			while ((ar = archive_read_data_block(a, (const void **)&p,
										   &size, &off)) == ARCHIVE_OK)
			{
				if (archive_write_data_block(t, p, size, off) != ARCHIVE_OK)
					err("failed to write image '%s': %s\n",
						fname, archive_error_string(t));
			}
			if (ar != ARCHIVE_EOF)
				err("failed reading gpkg member '%s': %s",
					fname, archive_error_string(a));
			archive_write_finish_entry(t);
		}
		if (ar != ARCHIVE_EOF)
			err("failed reading gpkg archive: %s",
				archive_error_string(a));
		archive_read_close(a);
		archive_read_free(a);
		if (archive_write_close(t) < ARCHIVE_WARN)
			err("failed to finalize gpkg extraction: %s",
				archive_error_string(t));
		archive_write_free(t);
		xchdir("..");
#else
		err("gpkg support not compiled in for %s", p);
#endif
	} else {
		int             vdbfd;
		int             mfd;
		file_magic_type fmt;
		struct qm_xpak_extract_ctx xc;

		snprintf(buf, sizeof(buf), "%s/%s", portroot, p);

		tbz2size = 0;
		if ((vdbfd = open("vdb", O_RDONLY)) == -1)
			err("failed to open vdb extraction directory");
		xc.fd = vdbfd;
		xc.error = false;
		tbz2size = xpak_extract(buf, &xc, pkg_extract_xpak_cb);
		close(vdbfd);
		if (tbz2size <= 0 || xc.error)
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
											   ARCHIVE_EXTRACT_XATTR |
									   	   ARCHIVE_EXTRACT_SECURE_SYMLINKS |
									   	   ARCHIVE_EXTRACT_SECURE_NODOTDOT |
									   	   ARCHIVE_EXTRACT_SECURE_NOABSOLUTEPATHS));
			if (archive_read_open(a, &stream, NULL,
								  qm_tar_read_cb, NULL) != ARCHIVE_OK)
				err("failed to open binpkg %s: %s",
					p, archive_error_string(a));
			while ((r = archive_read_next_header(a, &entry)) == ARCHIVE_OK) {
				if (archive_write_header(t, entry) != ARCHIVE_OK)
					err("failed to unpack binpkg '%s': %s",
						archive_entry_pathname(entry),
						archive_error_string(t));
				while ((r = archive_read_data_block(a, &dblk,
											   &dsize, &doff)) == ARCHIVE_OK)
				{
					if (archive_write_data_block(t, dblk,
												 dsize, doff) != ARCHIVE_OK)
						err("failed to write binpkg '%s': %s\n",
							archive_entry_pathname(entry),
							archive_error_string(t));
				}
				if (r != ARCHIVE_EOF)
					err("failed reading binpkg '%s': %s",
						archive_entry_pathname(entry),
						archive_error_string(a));
				archive_write_finish_entry(t);
			}
			if (r != ARCHIVE_EOF)
				err("failed to unpack binpkg %s: %s",
					p, archive_error_string(a));
			archive_read_close(a);
			archive_read_free(a);
			if (archive_write_close(t) < ARCHIVE_WARN)
				err("failed to finalize binpkg extraction: %s",
					archive_error_string(t));
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

	{
		static char pp[_Q_PATH_MAX];

		snprintf(pp, sizeof(pp), "%s/%s", matom->CATEGORY, matom->PF);
		qm_phase_pkg = pp;
	}

	if (!pretend) {
		pkg_run_func("vdb", pm_phases, PKG_PRETEND, D, T, eapi, replver);
		pkg_run_func("vdb", pm_phases, PKG_SETUP,   D, T, eapi, replver);
		pkg_run_func("vdb", pm_phases, PKG_PREINST, D, T, eapi, replver);
	}

	{
		int imagefd = open("image", O_RDONLY);
		  /* worst case scenario */
		size_t masklen = strlen(install_mask) + 1 +
				strlen(pkg_install_mask) + 1 +
				15 + 1 + 14 + 1 + 14 + 1 + 1;
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

	/* refuse before prerm/unmerge/merge run: an abort here leaves the
	 * installed system completely untouched */
	if (!pretend)
		qm_collision_protect(matom, slotmembers, eprefix_len,
				cp_argc, cp_argv, cpm_argc, cpm_argv);

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

		cpath = xstrdup("");

		/* the replaced instance's recorded md5 map drives
		 * config-protect-if-modified and admin-deleted offers */
		qm_cfg_oldmd5_load(previnst);

		/* downgrades always ignore config memory, exactly like
		 * portage forces --noconfmem for them */
		qm_cfg_noconfmem = getenv("NOCONFMEM") != NULL ||
				replacing == OLDER;

		ret = merge_tree_at(AT_FDCWD, "image",
				AT_FDCWD, portroot, contents, eprefix_len,
				&objs, &cpath, cp_argc, cp_argv, cpm_argc, cpm_argv);

		free(cpath);

		if (ret != 0)
			errp("failed to merge to %s", portroot);

		{
			int cerr = ferror(contents);
			if (fclose(contents) != 0 || cerr)
				errp("failed to finalize vdb/CONTENTS for %s/%s",
						matom->CATEGORY, matom->PF);
		}

		qm_confmem_write();
	}

	/* Unmerge any stray pieces from the versions we replaced.
	 * A slot holds one package, so remove EVERY installed member of the slot
	 * (there is normally one; more only when a prior install corrupted
	 * the slot).
	 * Files owned by the incoming package (objs) are kept, so
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

				if (!pretend && qm_preserve_active())
					pres_paths = qm_preserve_compute(slotmembers,
													 mpkg, objs);
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
		array_free(slotmembers);
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

	/* Update the magic counter.
	 * Portage assigns every install a unique, strictly increasing COUNTER 
	 * (vardbapi.counter_tick_core); a value that is too low corrupts 
	 * slot ordering and AUTOCLEAN.
	 * Only tick the global counter for a real merge, pretend must 
	 * not mutate the DB. */
	if (!pretend) {
		long counter = qm_counter_tick();
		bool cok = false;
		if ((fp = fopen("vdb/COUNTER", "w")) != NULL) {
			cok = fprintf(fp, "%ld", counter) >= 0;
			if (fclose(fp) != 0)
				cok = false;
		}
		if (!cok)
			errp("failed to write vdb/COUNTER for %s/%s",
					matom->CATEGORY, matom->PF);
		if (pres_paths != NULL) {
			char cntbuf[24];
			char ncpv[512];

			snprintf(cntbuf, sizeof(cntbuf), "%ld", counter);
			snprintf(ncpv, sizeof(ncpv), "%s/%s",
					 matom->CATEGORY, matom->PF);
			preserved_register(qm_preserved_get(), ncpv,
							   matom->SLOT ? : "0", cntbuf, pres_paths);
		}
	}
	if (pres_paths != NULL) {
		array_deepfree(pres_paths, free);
		pres_paths = NULL;
	}

	/* Record BINPKGMD5: the md5 of the binary package we installed from,
	 * exactly as Portage does (lib/_emerge/Binpkg.py).
	 * It lets Portage identify which binpkg instance produced this 
	 * install & detect a same-version rebuild (different content). */
	if (!pretend) {
		char  *bpp = tree_pkg_get_path(mpkg);
		char  *md5;
		if (bpp != NULL) {
			/* same construction the unpack path uses above */
			snprintf(buf, sizeof(buf), "%s/%s", portroot, bpp);
			/* hash_file returns a static buffer, do not free it */
			md5 = hash_file(buf, HASH_MD5);
			if (md5 != NULL) {
				bool ok = false;
				if ((fp = fopen("vdb/BINPKGMD5", "w")) != NULL) {
					ok = fprintf(fp, "%s\n", md5) >= 0;
					if (fclose(fp) != 0)
						ok = false;
				}
				if (!ok)
					errp("failed to write vdb/BINPKGMD5 for %s/%s",
							matom->CATEGORY, matom->PF);
			}
		}
	}

	/* Record INSTALL_MASK actually applied, matching Portage
	 * (lib/portage/dbapi/bintree.py); used for reinstall detection when
	 * the mask changes. */
	if (!pretend && install_mask != NULL) {
		bool ok = false;
		if ((fp = fopen("vdb/INSTALL_MASK", "w")) != NULL) {
			ok = fprintf(fp, "%s\n", install_mask) >= 0;
			if (fclose(fp) != 0)
				ok = false;
		}
		if (!ok)
			warnp("could not record vdb/INSTALL_MASK for %s/%s",
					matom->CATEGORY, matom->PF);
	}

	if (!pretend) {
		size_t len;
		size_t tlen;
		bool   fastok;
		char   vdbtmp[_Q_PATH_MAX + 64];
		/* move the local vdb copy to the final place */
		len = snprintf(buf, sizeof(buf), "%s%s/%s",
				portroot, portvdb, matom->CATEGORY);
		mkdir_p(buf, 0755);
		tlen = snprintf(vdbtmp, sizeof(vdbtmp), "%s/.qmerge-%u-",
				buf, (unsigned)getpid());
		snprintf(vdbtmp + tlen, sizeof(vdbtmp) - tlen, "%s", matom->PF);
		snprintf(buf + len, sizeof(buf) - len, "/%s", matom->PF);

		rm_rf(vdbtmp);
		fastok = rename("vdb", vdbtmp) == 0;
		if (!fastok) {
			struct stat     vst;
			int             src_fd = -1;
			int             dst_fd = -1;
			int             cnt    = 0;
			int             vi;
			struct dirent **files  = NULL;
			bool            copyok = false;

			/* e.g. in case of cross-device rename, try copy+delete */
			if ((src_fd = open("vdb", O_RDONLY|O_CLOEXEC|O_PATH)) >= 0 &&
				fstat(src_fd, &vst) == 0 &&
				mkdir_p(vdbtmp, vst.st_mode) == 0 &&
				(dst_fd = open(vdbtmp, O_RDONLY|O_CLOEXEC|O_PATH)) >= 0 &&
				(cnt = scandirat(src_fd, ".",
								 &files, filter_self_parent, NULL)) >= 0)
			{
				/* for now we assume the VDB is a flat directory, e.g.
				 * there are no subdirs */
				copyok = true;
				for (vi = 0; vi < cnt; vi++) {
					if (move_file(src_fd, files[vi]->d_name,
							  	  dst_fd, files[vi]->d_name,
							  	  NULL) != 0) {
						warn("failed to move 'vdb/%s' to '%s': %s",
							 files[vi]->d_name, vdbtmp, strerror(errno));
						copyok = false;
					}
				}
				scandir_free(files, cnt);
			}
			if (src_fd >= 0)
				close(src_fd);
			if (dst_fd >= 0)
				close(dst_fd);
			if (!copyok) {
				rm_rf(vdbtmp);
				err("failed to record VDB for %s/%s",
						matom->CATEGORY, matom->PF);
			}
		}

		rm_rf(buf);
		if (rename(vdbtmp, buf) != 0) {
			rm_rf(vdbtmp);
			errp("failed to install VDB %s", buf);
		}
	}

	/* clean up our local temp dir */
	xchdir("..");
	if (!keep_work)
		rm_rf(matom->PF);
	/* don't care about return, but when empty, remove */
	rmdir("../qmerge");

	/* merge-list line colors: one magenta run for the whole atom (bold for
	 * the explicit target, plain for deps), the [repo] tag like the
	 * pretend display. gentoo mode. we prefer it this way as well. */
	{
		const char *pc  = *NORM == '\0' ? "" :
						  level == 0 ? "\033[35;01m" : MAGENTA;
		char       *rep = tree_pkg_meta(mpkg, Q_repository);
		const char *rn  = qm_nbinrepos > 1 ?
						  qm_repo_name_of_pkg(mpkg) : NULL;

		printf("%s>>>%s Installing (%zu of %zu) %s%s/%s",
				GREEN, NORM,
				qm_mg_total > 0 ? qm_mg_n : 1,
				qm_mg_total > 0 ? qm_mg_total : 1,
				pc, matom->CATEGORY, matom->PF);
		if (matom->SLOT != NULL) {
			printf(":%s", matom->SLOT);
			if (matom->SUBSLOT != NULL &&
					strcmp(matom->SLOT, matom->SUBSLOT) != 0)
				printf("/%s", matom->SUBSLOT);
		}
		if (rep != NULL && *rep != '\0')
			printf("::%s", rep);
		printf("%s", NORM);
		if (rn != NULL)
			printf(" %s[%s]%s",
				   qm_repo_tag_color_b(level == 0), rn, NORM);
		printf("\n");
	}

	if (level == 0 && !pretend)
		qm_elog(" ::: completed emerge (%zu of %zu) %s to %s",
				qm_mg_total > 0 ? qm_mg_n : 1,
				qm_mg_total > 0 ? qm_mg_total : 1,
				atom_format("%[CAT]%[PF]", matom), portroot);

	/* portage runs env_update after every merge (vartree treewalk);
	 * the freshly written CONTENTS feeds the ldconfig gate,
	 * so we will do the exact same. */
	if (!pretend) {
		char    cpath[_Q_PATH_MAX];
		char   *cbuf    = NULL;
		size_t  clen    = 0;
		array  *touched = NULL;

		snprintf(cpath, sizeof(cpath), "%s%s/%s/%s/CONTENTS",
				 portroot, portvdb, matom->CATEGORY, matom->PF);
		if (eat_file(cpath, &cbuf, &clen)) {
			char *line;
			char *savep;

			touched = array_new();
			for (line = strtok_r(cbuf, "\n", &savep);
				 line != NULL;
				 line = strtok_r(NULL, "\n", &savep))
			{
				contents_entry *e = contents_parse_line(line);

				if (e != NULL && (e->type == CONTENTS_OBJ ||
								  e->type == CONTENTS_SYM))
					array_append(touched, xstrdup(e->name));
			}
		}
		free(cbuf);
		qm_env_update_hook(touched);
		if (touched != NULL)
			array_deepfree(touched, free);
	}
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
			buf = q_deconst("0");
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
	contentsp = xstrdup(contentsp);

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
					if (hash != NULL)
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

		/* a path this unmerge releases (no other owner keeps it)
		 * drops its config-memory entry, portage's stale-confmem rule */
		if (!pretend &&
				(keep == NULL || contains_set(e->name, keep) == NULL) &&
				qm_confmem_has(e->name))
			qm_confmem_del(e->name);

		snprintf(zing, sizeof(zing), "%s%s%s",
				protected ? YELLOW : GREEN,
				protected ? "***" : "<<<" , NORM);

		if (protected) {
			qprintf("%s %s\n", zing, e->name);
			continue;
		}

		/* See if this file is owned by the incoming package (or by any
		 * other slot member being merged): if so, keep it.
		 * Use a non-destructive membership test, del_set() would REMOVE the
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

	qm_confmem_write();

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
			buf = q_deconst("0");
		phases = tree_pkg_meta(pkg_ctx, Q_DEFINED_PHASES);
		if (phases != NULL) {
			mkdir_p(T, 0755);
			pkg_run_func_at(portroot_fd, tree_pkg_get_path(pkg_ctx),
							phases, PKG_POSTRM,
							T, T, buf, rpkg == NULL ? "" : rpkg->PVR);
		}

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

	/* portage runs env_update after every unmerge too. A replace
	 * (rpkg set) is covered by the merge-side hook right after */
	if (!pretend && rpkg == NULL) {
		char *cts = tree_pkg_meta(pkg_ctx, Q_CONTENTS);

		if (cts != NULL) {
			char   *cbuf    = xstrdup(cts);
			array  *touched = array_new();
			char   *line;
			char   *csavep;

			for (line = strtok_r(cbuf, "\n", &csavep);
				 line != NULL;
				 line = strtok_r(NULL, "\n", &csavep))
			{
				contents_entry *e = contents_parse_line(line);

				if (e != NULL && (e->type == CONTENTS_OBJ ||
								  e->type == CONTENTS_SYM))
					array_append(touched, xstrdup(e->name));
			}
			qm_env_update_hook(touched);
			array_deepfree(touched, free);
			free(cbuf);
		} else {
			qm_env_update_hook(NULL);
		}
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
	if (fd != -1 && fstat(fd, &st) != -1) {
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
	const char *k;
	const char *sortk;
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
	/* relpath -> qm_oldblock, entries eligible for reuse */
	set    *old;
	/* struct qm_entry, sorted before writing */
	array  *entries;
	/* struct qm_rr pairs seen in package metadata */
	array  *rrs;
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
	/* the entry block, verbatim */
	char      raw[];
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
		bool                md5  = false;

		end = strstr(blk, "\n\n");
		if (end == NULL)
			end = blk + strlen(blk);
		else
			/* keep the final newline of the block */
			end += 1;

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
			else if (strncmp(line, "MD5: ", 5) == 0)
				md5 = true;
		}
		free(tmp);

		/* like emaint: an entry without MD5 is rebuilt, never reused */
		if (path != NULL && ob->mtime >= 0 && ob->size >= 0 && md5) {
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

/* filename -> cpv parsing (qbh_*) lives in libq/binpath.c so it can
 * be fuzzed on its own; the PATH strings it consumes come from a
 * remote Packages index and are untrusted. */

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

	{
		char *vcpv = binpath_rel_cpv(relpath);

		if (vcpv == NULL) {
			fprintf(stderr,
					"\n!!! Binary package name is invalid: '%s%s'\n",
					portroot, tree_pkg_get_path(pkg));
			return 0;
		}
		free(vcpv);
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

/* portage's index lock: fcntl F_WRLCK on $PKGDIR/.Packages.portage_lockfile,
 * unlink-before-release, Record locks * are per-process, 
 * die with any close of the file. 
 * we finally have a locking mechanism, 4 years later */
static int  qm_pkgindex_lockfd = -1;
static char qm_pkgindex_lockp[_Q_PATH_MAX + 48];

static int
qm_pkgindex_lock(const char *pdir)
{
	bool warned = false;

	snprintf(qm_pkgindex_lockp, sizeof(qm_pkgindex_lockp),
			 "%s/.%s.portage_lockfile", pdir, Packages);
	for (;;) {
		mode_t       om;
		int          fd;
		struct flock fl;
		struct stat  fst;
		struct stat  pst;

		om = umask(0);
		fd = open(qm_pkgindex_lockp, O_CREAT | O_RDWR | O_CLOEXEC, 0660);
		umask(om);
		if (fd < 0) {
			warnp("cannot open %s", qm_pkgindex_lockp);
			return -1;
		}
		memset(&fl, 0, sizeof(fl));
		fl.l_type   = F_WRLCK;
		fl.l_whence = SEEK_SET;
		if (fcntl(fd, F_SETLK, &fl) != 0) {
			if (errno != EACCES && errno != EAGAIN) {
				warnp("cannot lock %s", qm_pkgindex_lockp);
				close(fd);
				return -1;
			}
			if (!warned) {
				warned = true;
				qprintf("waiting for lock on %s (emerge/quickpkg running?)\n",
						qm_pkgindex_lockp);
			}
			while (fcntl(fd, F_SETLKW, &fl) != 0) {
				if (errno == EINTR)
					continue;
				warnp("cannot lock %s", qm_pkgindex_lockp);
				close(fd);
				return -1;
			}
		}
		if (fstat(fd, &fst) != 0 ||
				stat(qm_pkgindex_lockp, &pst) != 0 ||
				pst.st_dev != fst.st_dev || pst.st_ino != fst.st_ino) {
			close(fd);
			continue;
		}
		qm_pkgindex_lockfd = fd;
		return fd;
	}
}

static void
qm_pkgindex_unlock(void)
{
	if (qm_pkgindex_lockfd < 0)
		return;
	unlink(qm_pkgindex_lockp);
	close(qm_pkgindex_lockfd);
	qm_pkgindex_lockfd = -1;
}

/* qmaint binhost --fix should touch only the index */
static bool qm_regen_transports = true;

static int
binpkg_index_regen(void)
{
	struct qm_idx_state st;
	tree_ctx           *bin;
	FILE               *out;
	FILE               *body;
	int                 ret;
	bool                gzfail = false;
	time_t              idxts = 0;
	char                pdir[_Q_PATH_MAX];
	char                finp[_Q_PATH_MAX + 16];
	char                oldp[_Q_PATH_MAX + 32];
	char                newp[_Q_PATH_MAX + 32];
	char                tmpp[_Q_PATH_MAX + 32];
	char                buf[BUFSIZ];
	size_t              n;
	bool                hadold;
	set                *oldset;
	array              *oldmem;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	snprintf(finp, sizeof(finp), "%s/%s", pdir, Packages);
	snprintf(oldp, sizeof(oldp), "%.4095s.regen-old", finp);
	snprintf(newp, sizeof(newp), "%.4095s.regen-new", finp);
	snprintf(tmpp, sizeof(tmpp), "%.4095s.regen-tmp", finp);

	/* this is a concurrent serialization of emerge/quickpkg inject() 
	 * hopefully */
	if (qm_pkgindex_lock(pdir) < 0)
		warn("proceeding without index lock");

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
	{
		int werr = ferror(st.fp);
		if (fclose(st.fp) != 0)
			werr = 1;
		tree_close(bin);
		if (werr) {
			warnp("cannot write %s", newp);
			goto fail;
		}
	}

	/* final index = header + body */
	out = fopen(tmpp, "w");
	if (out == NULL) {
		warnp("cannot open %s for writing", tmpp);
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
				hdr[nh].v     = q_deconst(V); \
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
		idxts = time(NULL);
		snprintf(tsbuf, sizeof(tsbuf), "%zu", (size_t)idxts);
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
	if (body == NULL) {
		warnp("cannot open %s for reading", newp);
		fclose(out);
		goto fail;
	}
	while ((n = fread(buf, 1, sizeof(buf), body)) > 0) {
		if (fwrite(buf, 1, n, out) != n) {
			warnp("cannot write %s", tmpp);
			fclose(body);
			fclose(out);
			goto fail;
		}
	}
	if (ferror(body)) {
		warnp("cannot read %s", newp);
		fclose(body);
		fclose(out);
		goto fail;
	}
	fclose(body);
	{
		int werr = fflush(out) != 0;
		if (fclose(out) != 0)
			werr = 1;
		if (werr) {
			warnp("cannot finalize %s", tmpp);
			goto fail;
		}
	}
	unlink(newp);

	/* stamp mode + TIMESTAMP mtime on the temp before the swap, so the
	 * live index carries them the instant it appears (rename keeps the
	 * mtime). emaint/qmaint binhost --check wants both index mtimes equal. */
	binpkg_perms(tmpp, false);
	{
		struct timespec its[2] = { { idxts, 0 }, { idxts, 0 } };

		utimensat(AT_FDCWD, tmpp, its, 0);

		if (rename(tmpp, finp) != 0) {
			warnp("cannot install %s", finp);
			unlink(tmpp);
			goto fail;
		}
		if (hadold)
			unlink(oldp);

		/* FEATURES=compress-index: maintain the Packages.gz twin the
		 * way portage does, from the exact same content, also via a
		 * temp + atomic rename */
		{
			char gzp[_Q_PATH_MAX + 32];
			char gztmp[_Q_PATH_MAX + 48];

			snprintf(gzp, sizeof(gzp), "%.4095s.gz", finp);
			snprintf(gztmp, sizeof(gztmp), "%.4095s.gz.regen-tmp", finp);
			if (contains_set("compress-index", features)) {
				FILE   *fin = fopen(finp, "r");
				gzFile  gz  = gzopen(gztmp, "wb9");

				if (fin == NULL || gz == NULL)
					gzfail = true;
				if (fin != NULL && gz != NULL) {
					char   gbuf[BUFSIZ];
					size_t gn;

					while ((gn = fread(gbuf, 1, sizeof(gbuf), fin)) > 0) {
						if (gzwrite(gz, gbuf, (unsigned)gn) != (int)gn) {
							gzfail = true;
							break;
						}
					}
					if (ferror(fin))
						gzfail = true;
				}
				if (gz != NULL && gzclose(gz) != Z_OK)
					gzfail = true;
				if (fin != NULL)
					fclose(fin);
				if (!gzfail) {
					binpkg_perms(gztmp, false);
					utimensat(AT_FDCWD, gztmp, its, 0);
					if (rename(gztmp, gzp) != 0) {
						warnp("cannot install %s", gzp);
						unlink(gztmp);
						gzfail = true;
					}
				} else {
					warn("compress-index: %s not updated", gzp);
					unlink(gztmp);
				}
			} else {
				unlink(gzp);
			}
		}
	}

	if (qm_regen_transports) {
		int edfd = open(pdir, O_RDONLY | O_DIRECTORY | O_CLOEXEC);

		qm_emit_moves(edfd, pdir);
		qm_emit_news(edfd, pdir);
		if (edfd >= 0)
			close(edfd);
	}

	qprintf("%s>>>%s indexed %zu binpkg%s (%zu reused) in %s\n",
			GREEN, NORM, st.count, st.count == 1 ? "" : "s",
			st.reused, pdir);
	ret = gzfail ? EXIT_FAILURE : EXIT_SUCCESS;
	goto out;

 fail:
	unlink(newp);
	unlink(tmpp);
	if (hadold && rename(oldp, finp) != 0)
		warnp("failed to restore previous %s", finp);
	ret = EXIT_FAILURE;

 out:
	qm_pkgindex_unlock();
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

/* qmaint binhost: emaint binhost --check/--fix semantics.
 * near-perfect clone of emaint, with MTIME, sizes, MD5-present, 
 * binpkg_index_regen will do the trick, and match everything
 * emaint repairs. */

static bool qbh_quiet_invalid = false;

struct qbh_pf {
	char     *rel;
	char     *cpv;
	long long mtime;
	long long size;
};

struct qbh_ie {
	char     *cpv;
	char     *path;
	long long mtime;
	long long size;
	bool      has_md5;
	bool      claimed;
};

static void
qbh_scan_file(array *files, const char *pdir, const char *rel)
{
	struct qbh_pf *f;
	char           fpath[_Q_PATH_MAX * 4];
	const char    *base;
	size_t         blen;
	struct stat    st;
	char          *cpv;

	snprintf(fpath, sizeof(fpath), "%s/%s", pdir, rel);
	if (stat(fpath, &st) != 0 || !S_ISREG(st.st_mode))
		return;

	base = strrchr(rel, '/');
	base = base != NULL ? base + 1 : rel;
	if (binpath_strip_ext(base, &blen) == NULL)
		return; 

	cpv = binpath_rel_cpv(rel);
	if (cpv == NULL) {
		/* portage style complaint. should be quiet
		 * in fix mode */
		if (!qbh_quiet_invalid)
			fprintf(stderr,
					"\n!!! Binary package name is invalid: '%s'\n",
					fpath + (fpath[0] == '/' && fpath[1] == '/' ? 1 : 0));
		return;
	}

	f = xzalloc(sizeof(*f));
	f->rel   = xstrdup(rel);
	f->cpv   = cpv;
	f->mtime = (long long)st.st_mtime;
	f->size  = (long long)st.st_size;
	array_append(files, f);
}

static void
qbh_scan(const char *pdir, array *files)
{
	DIR           *cd = opendir(pdir);
	struct dirent *ce;

	if (cd == NULL)
		return;
	while ((ce = readdir(cd)) != NULL) {
		char           cpath[_Q_PATH_MAX * 2];
		char           rel[_Q_PATH_MAX * 2];
		struct stat    cst;
		DIR           *pd;
		struct dirent *pe;

		if (ce->d_name[0] == '.')
			continue;
		snprintf(cpath, sizeof(cpath), "%s/%s", pdir, ce->d_name);
		if (stat(cpath, &cst) != 0 || !S_ISDIR(cst.st_mode))
			continue;
		pd = opendir(cpath);
		if (pd == NULL)
			continue;
		while ((pe = readdir(pd)) != NULL) {
			char        ppath[_Q_PATH_MAX * 3];
			struct stat pst;

			if (pe->d_name[0] == '.')
				continue;
			snprintf(ppath, sizeof(ppath), "%.4095s/%s", cpath, pe->d_name);
			if (stat(ppath, &pst) != 0)
				continue;
			if (S_ISDIR(pst.st_mode)) {
				DIR           *fd_ = opendir(ppath);
				struct dirent *fe;

				if (fd_ == NULL)
					continue;
				while ((fe = readdir(fd_)) != NULL) {
					if (fe->d_name[0] == '.')
						continue;
					snprintf(rel, sizeof(rel), "%s/%s/%s",
							 ce->d_name, pe->d_name, fe->d_name);
					qbh_scan_file(files, pdir, rel);
				}
				closedir(fd_);
			} else {
				snprintf(rel, sizeof(rel), "%s/%s",
						 ce->d_name, pe->d_name);
				qbh_scan_file(files, pdir, rel);
			}
		}
		closedir(pd);
	}
	closedir(cd);
}

static array *
qbh_load(const char *file, set **bypath)
{
	char   *buf = NULL;
	size_t  len = 0;
	char   *blk;
	char   *end;
	array  *ret;

	*bypath = NULL;
	if (!eat_file(file, &buf, &len) || buf == NULL) {
		free(buf);
		return NULL;
	}

	ret     = array_new();
	*bypath = create_set();

	blk = strstr(buf, "\n\n");
	if (blk == NULL) {
		free(buf);
		return ret;
	}
	blk += 2;

	while (*blk != '\0') {
		struct qbh_ie *ie;
		char          *tmp;
		char          *line;
		char          *sp;

		end = strstr(blk, "\n\n");
		if (end == NULL)
			end = blk + strlen(blk);

		ie = xzalloc(sizeof(*ie));
		ie->mtime = -1;
		ie->size  = -1;

		{
			size_t blen = (size_t)(end - blk);

			tmp = xmalloc(blen + 1);
			memcpy(tmp, blk, blen);
			tmp[blen] = '\0';
		}
		for (line = strtok_r(tmp, "\n", &sp);
			 line != NULL;
			 line = strtok_r(NULL, "\n", &sp))
		{
			if (strncmp(line, "CPV: ", 5) == 0 && ie->cpv == NULL)
				ie->cpv = xstrdup(line + 5);
			else if (strncmp(line, "PATH: ", 6) == 0 && ie->path == NULL)
				ie->path = xstrdup(line + 6);
			else if (strncmp(line, "MTIME: ", 7) == 0)
				ie->mtime = atoll(line + 7);
			else if (strncmp(line, "SIZE: ", 6) == 0)
				ie->size = atoll(line + 6);
			else if (strncmp(line, "MD5: ", 5) == 0)
				ie->has_md5 = true;
		}
		free(tmp);

		if (ie->cpv == NULL) {
			free(ie->path);
			free(ie);
		} else {
			array_append(ret, ie);
			if (ie->path != NULL) {
				void *prev = NULL;
				add_set_value(ie->path, ie, &prev, *bypath);
			}
		}

		while (*end == '\n')
			end++;
		blk = end;
	}

	free(buf);
	return ret;
}

static int
qbh_pf_cmp(const void *a, const void *b)
{
	const struct qbh_pf *fa = *(const struct qbh_pf * const *)a;
	const struct qbh_pf *fb = *(const struct qbh_pf * const *)b;
	int r = strcmp(fa->cpv, fb->cpv);

	return r != 0 ? r : strcmp(fa->rel, fb->rel);
}

/* env-update, a fair port of portage's util/env_update.py.
 * Deliberately not ported: prelink.conf (dead ftm) and the
 * EPREFIX bfd /usr/etc/ld.so.conf variant. The env.d / ld.so.conf
 * parsers live in libq/envd.c so they can be fuzzed on their own. */

static void
qm_env_write_atomic(const char *path, const char *content, bool *changed)
{
	char    tmp[_Q_PATH_MAX + 16];
	char   *old  = NULL;
	size_t  olen = 0;
	FILE   *f;

	if (eat_file(path, &old, &olen) && old != NULL &&
			strcmp(old, content) == 0)
	{
		free(old);
		return;
	}
	free(old);

	if (changed != NULL)
		*changed = true;
	snprintf(tmp, sizeof(tmp), "%s.qmtmp", path);
	f = fopen(tmp, "w");
	if (f == NULL) {
		warnp("cannot write %s", path);
		return;
	}
	fputs(content, f);
	if (fclose(f) != 0 || rename(tmp, path) != 0) {
		warnp("cannot finish %s", path);
		unlink(tmp);
	}
}

static void
qm_norm_path(char *p)
{
	char *r = p;
	char *w = p;

	while (*r != '\0') {
		if (*r == '/' && r[1] == '/') {
			r++;
			continue;
		}
		*w++ = *r++;
	}
	if (w > p + 1 && w[-1] == '/')
		w--;
	*w = '\0';
}

/* mtime cache in the spirit of portage's mtimedb["ldpath"];
 * text lines "mtime path" */
static hash_t *
qm_ldpath_cache_load(const char *path)
{
	hash_t *ret  = hash_new();
	char   *buf  = NULL;
	size_t  blen = 0;
	char   *line;
	char   *savep;

	if (!eat_file(path, &buf, &blen)) {
		free(buf);
		return ret;
	}
	for (line = strtok_r(buf, "\n", &savep);
		 line != NULL;
		 line = strtok_r(NULL, "\n", &savep))
	{
		char *sp = strchr(line, ' ');

		if (sp == NULL)
			continue;
		*sp = '\0';
		hash_add(ret, sp + 1, xstrdup(line), NULL);
	}
	free(buf);
	return ret;
}

/* the env-update engine. check_only reports staleness without
 * writing; always_ldconfig mirrors the env-update CLI (no contents
 * gate). touched is the just-(un)merged CONTENTS obj/sym paths for
 * portage's skip-ldconfig-when-no-lib-changed optimisation, NULL
 * disables the gate.Returns nonzero when something was (or, in
 * check mode, would be) rewritten.  */ 
static int
qm_env_update(bool check_only, bool always_ldconfig, bool no_ldconfig,
			  array *touched)
{
	char             path[_Q_PATH_MAX * 2];
	char             envd[_Q_PATH_MAX];
	struct dirent  **dents;
	int              dcnt;
	int              di;
	array           *config_list = array_new();
	set             *space_sep   = create_set();
	set             *colon_sep   = create_set();
	array           *env_keys    = array_new();
	hash_t          *env         = hash_new();
	array           *ldpath      = array_new();
	set             *lib_dirs    = NULL;
	bool             wrote       = false;
	bool             mtime_changed = false;
	bool             makelinks   = true;
	size_t           i;
	size_t           n;
	char            *k;
	static const char *space_init[] =
		{ "CONFIG_PROTECT", "CONFIG_PROTECT_MASK" };
	static const char *colon_init[] = {
		"ADA_INCLUDE_PATH", "ADA_OBJECTS_PATH", "CLASSPATH", "INFODIR",
		"INFOPATH", "KDEDIRS", "LDPATH", "MANPATH", "PATH",
		"PKG_CONFIG_PATH", "PRELINK_PATH", "PRELINK_PATH_MASK",
		"PYTHONPATH", "ROOTPATH" };

	for (i = 0; i < ARRAY_SIZE(space_init); i++)
		space_sep = add_set_unique(space_init[i], space_sep, NULL);
	for (i = 0; i < ARRAY_SIZE(colon_init); i++)
		colon_sep = add_set_unique(colon_init[i], colon_sep, NULL);

	snprintf(envd, sizeof(envd), "%setc/env.d", portroot);
	mkdir_p(envd, 0755);

	dcnt = scandir(envd, &dents, NULL, alphasort);
	for (di = 0; di < dcnt; di++) {
		const char *fn = dents[di]->d_name;
		size_t      fl = strlen(fn);
		array      *kvs;
		size_t      ki;
		struct envd_kv *kv;

		if (fl < 3 ||
				!isdigit((unsigned char)fn[0]) ||
				!isdigit((unsigned char)fn[1]) ||
				fn[0] == '.' || fn[fl - 1] == '~' ||
				(fl > 4 && strcmp(fn + fl - 4, ".bak") == 0))
			continue;
		snprintf(path, sizeof(path), "%s/%s", envd, fn);
		kvs = envd_parse(path);
		if (kvs == NULL)
			continue;

		/* env.d files may extend the separator classes themselves */
		array_for_each(kvs, ki, kv) {
			char *tok;
			char *sp;

			if (strcmp(kv->k, "SPACE_SEPARATED") == 0 ||
					strcmp(kv->k, "COLON_SEPARATED") == 0)
			{
				set **tgt = kv->k[0] == 'S' ? &space_sep : &colon_sep;

				for (tok = strtok_r(kv->v, " \t", &sp);
					 tok != NULL;
					 tok = strtok_r(NULL, " \t", &sp))
					*tgt = add_set_unique(tok, *tgt, NULL);
				free(kv->k);
				kv->k = xstrdup("");
			}
		}
		array_append(config_list, kvs);
	}
	if (dcnt >= 0)
		scandir_free(dents, dcnt);

	/* cumulative vars: file order, first occurrence wins the dedup,
	 * joined with their separator; consumed from the per-file lists */
	{
		set   *seps[2] = { space_sep, colon_sep };
		char   sepc[2] = { ' ', ':' };
		int    si;

		for (si = 0; si < 2; si++) {
			array *vars = set_keys(seps[si]);
			char  *var;

			array_for_each(vars, n, var) {
				set    *seen = create_set();
				char    out[_Q_PATH_MAX * 8] = "";
				size_t  olen = 0;
				array  *kvs;
				size_t  ci;

				array_for_each(config_list, ci, kvs) {
					size_t             ki;
					struct envd_kv *kv;

					array_for_each(kvs, ki, kv) {
						char *tok;
						char *sp;
						char  sepstr[2] = { sepc[si], '\0' };

						if (strcmp(kv->k, var) != 0)
							continue;
						for (tok = strtok_r(kv->v, sepstr, &sp);
							 tok != NULL;
							 tok = strtok_r(NULL, sepstr, &sp))
						{
							if (*tok == '\0' ||
									contains_set(tok, seen) != NULL)
								continue;
							add_set_unique(tok, seen, NULL);
							if (olen + strlen(tok) + 2 < sizeof(out)) {
								if (olen > 0)
									out[olen++] = sepc[si];
								olen += (size_t)snprintf(out + olen,
										sizeof(out) - olen, "%s", tok);
							}
							if (strcmp(var, "LDPATH") == 0)
								array_append(ldpath, xstrdup(tok));
						}
						free(kv->k);
						kv->k = xstrdup("");
					}
				}
				if (olen > 0 && strcmp(var, "LDPATH") != 0) {
					void *prev = NULL;

					hash_add(env, var, xstrdup(out), &prev);
					free(prev);
					array_append(env_keys, xstrdup(var));
				}
				free_set(seen);
			}
			array_free(vars);
		}
	}

	{
		array *kvs;
		size_t ci;

		array_for_each(config_list, ci, kvs) {
			size_t             ki;
			struct envd_kv *kv;

			array_for_each(kvs, ki, kv) {
				void *prev = NULL;

				if (kv->k[0] == '\0' ||
						strcmp(kv->k, "LDPATH") == 0)
					continue;
				if (hash_get(env, kv->k) == NULL)
					array_append(env_keys, xstrdup(kv->k));
				hash_add(env, kv->k, xstrdup(kv->v), &prev);
				free(prev);
			}
		}
	}

	array_sort(env_keys, qm_strptr_cmp);

	/* ld.so.conf: rewrite only when the effective list changed */
	{
		char    lds[_Q_PATH_MAX];
		array  *cur;
		bool    same;
		char   *l;

		snprintf(lds, sizeof(lds), "%setc/ld.so.conf", portroot);
		cur  = envd_grabfile(lds);
		same = array_cnt(cur) == array_cnt(ldpath);
		if (same)
			array_for_each(cur, n, l)
				if (strcmp(l, (char *)array_get(ldpath, n)) != 0) {
					same = false;
					break;
				}
		array_deepfree(cur, free);

		if (!same) {
			char  *out;
			size_t olen = 128;
			size_t opos = 0;

			array_for_each(ldpath, n, l)
				olen += strlen(l) + 1;
			out  = xmalloc(olen);
			opos = (size_t)snprintf(out, olen,
					"# ld.so.conf autogenerated by env-update; make all "
					"changes to\n# contents of /etc/env.d directory.\n");
			array_for_each(ldpath, n, l)
				opos += (size_t)snprintf(out + opos, olen - opos,
										 "%s\n", l);
			if (check_only)
				wrote = true;
			else
				qm_env_write_atomic(lds, out, &wrote);
			free(out);
			mtime_changed = true;
		}
	}

	/* lib dir mtime scan (portage mtimedb["ldpath"] analogue) gating
	 * ldconfig; the same-second disambiguation is ported verbatim */
	if (!check_only) {
		char     cachep[_Q_PATH_MAX];
		hash_t  *cache;
		set     *scan   = NULL;
		array   *dirs;
		char    *d;
		time_t   now    = time(NULL);
		FILE    *cf;
		glob_t   g;

		lib_dirs = create_set();
		array_for_each(ldpath, n, d)
			scan = add_set_unique(d, scan, NULL);
		{
			static const char *pats[] = { "usr/lib*", "lib*" };

			for (i = 0; i < ARRAY_SIZE(pats); i++) {
				snprintf(path, sizeof(path), "%s%s", portroot, pats[i]);
				if (glob(path, 0, NULL, &g) == 0) {
					size_t gi;

					for (gi = 0; gi < g.gl_pathc; gi++) {
						const char *bn = strrchr(g.gl_pathv[gi], '/');

						if (bn != NULL &&
								strcmp(bn + 1, "libexec") == 0)
							continue;
						scan = add_set_unique(
								g.gl_pathv[gi] + strlen(portroot) - 1,
								scan, NULL);
					}
					globfree(&g);
				}
			}
		}
		snprintf(path, sizeof(path), "%setc/ld.so.conf", portroot);
		envd_read_ldsoconf(portroot, path, &scan);
		scan = add_set_unique("/usr/lib", scan, NULL);
		scan = add_set_unique("/lib", scan, NULL);
		{
			char *llp = hash_get(env, "LD_LIBRARY_PATH");

			if (llp != NULL) {
				char *tmp = xstrdup(llp);
				char *tok;
				char *sp;

				for (tok = strtok_r(tmp, ":", &sp);
					 tok != NULL;
					 tok = strtok_r(NULL, ":", &sp))
					if (*tok != '\0')
						scan = add_set_unique(tok, scan, NULL);
				free(tmp);
			}
		}

		snprintf(cachep, sizeof(cachep),
				 "%svar/cache/edb/qmerge_ldpath", portroot);
		cache = qm_ldpath_cache_load(cachep);

		dirs = set_keys(scan);
		array_for_each(dirs, n, d) {
			struct stat st;
			char        full[_Q_PATH_MAX];
			char        mstr[32];
			char       *prev;
			void       *ign = NULL;

			snprintf(full, sizeof(full), "%s%s", portroot,
					 d[0] == '/' ? d + 1 : d);
			qm_norm_path(full);
			if (stat(full, &st) != 0)
				continue;
			add_set_unique(full, lib_dirs, NULL);
			if (st.st_mtime == now) {
				struct timespec ts[2];

				st.st_mtime -= 1;
				ts[0].tv_sec  = st.st_mtime;
				ts[0].tv_nsec = 0;
				ts[1] = ts[0];
				utimensat(AT_FDCWD, full, ts, 0);
				mtime_changed = true;
			}
			snprintf(mstr, sizeof(mstr), "%lld",
					 (long long)st.st_mtime);
			prev = hash_get(cache, full);
			if (prev == NULL || strcmp(prev, mstr) != 0)
				mtime_changed = true;
			hash_add(cache, full, xstrdup(mstr), &ign);
			free(ign);
		}
		array_free(dirs);
		free_set(scan);

		cf = fopen(cachep, "w");
		if (cf != NULL) {
			array *ck = hash_keys(cache);
			char  *cp;

			array_for_each(ck, n, cp)
				fprintf(cf, "%s %s\n",
						(char *)hash_get(cache, cp), cp);
			array_free(ck);
			fclose(cf);
		}
		{
			array *cv = hash_values(cache);
			char  *cvp;

			array_for_each(cv, n, cvp)
				free(cvp);
			array_free(cv);
			hash_free(cache);
		}

		/* portage: no lib-dir mtime moved and the (un)merged package
		 * touched no file inside one -> ldconfig can be skipped */
		if (!always_ldconfig && !mtime_changed && touched != NULL) {
			bool  rel = false;
			char *tp;

			array_for_each(touched, n, tp) {
				char  dbuf[_Q_PATH_MAX];
				char *sl;

				snprintf(dbuf, sizeof(dbuf), "%s%s", portroot,
						 tp[0] == '/' ? tp + 1 : tp);
				qm_norm_path(dbuf);
				sl = strrchr(dbuf, '/');
				if (sl != NULL && sl != dbuf)
					*sl = '\0';
				if (contains_set(dbuf, lib_dirs) != NULL) {
					rel = true;
					break;
				}
			}
			if (!rel)
				makelinks = false;
		}
	}

	/* profile.env / environment.d / csh.env, sorted keys, LDPATH
	 * excluded; the $'...' corner reproduces portage verbatim */
	{
		size_t  cap = 4096;
		size_t  olen;
		char   *pout;
		char   *cout;
		char   *sout;
		size_t  ppos = 0;
		size_t  cpos = 0;
		size_t  spos = 0;

		array_for_each(env_keys, n, k)
			cap += 2 * strlen(k) + 2 * strlen((char *)hash_get(env, k))
				 + 64;
		olen = cap;
		pout = xmalloc(olen);
		cout = xmalloc(olen);
		sout = xmalloc(olen);

		ppos = (size_t)snprintf(pout, olen,
				"# THIS FILE IS AUTOMATICALLY GENERATED BY env-update.\n"
				"# DO NOT EDIT THIS FILE. CHANGES TO STARTUP PROFILES\n"
				"# GO INTO /etc/profile NOT /etc/profile.env\n\n");
		cpos = (size_t)snprintf(cout, olen,
				"# THIS FILE IS AUTOMATICALLY GENERATED BY env-update.\n"
				"# DO NOT EDIT THIS FILE. CHANGES TO STARTUP PROFILES\n"
				"# GO INTO /etc/csh.cshrc NOT /etc/csh.env\n\n");
		spos = (size_t)snprintf(sout, olen,
				"# THIS FILE IS AUTOMATICALLY GENERATED BY env-update.\n"
				"# DO NOT EDIT THIS FILE.\n\n");

		array_for_each(env_keys, n, k) {
			char *v = hash_get(env, k);

			if (v == NULL)
				continue;
			if (v[0] == '$' && v[1] != '{')
				ppos += (size_t)snprintf(pout + ppos, olen - ppos,
						"export %s=$'%s'\n", k, v + 1);
			else
				ppos += (size_t)snprintf(pout + ppos, olen - ppos,
						"export %s='%s'\n", k, v);
			cpos += (size_t)snprintf(cout + cpos, olen - cpos,
					"setenv %s '%s'\n", k, v);
			if (v[0] != '\0')
				spos += (size_t)snprintf(sout + spos, olen - spos,
						"%s=%s\n", k, v);
		}

		snprintf(path, sizeof(path), "%setc/profile.env", portroot);
		if (check_only) {
			char   *old  = NULL;
			size_t  ol   = 0;

			if (!eat_file(path, &old, &ol) || old == NULL ||
					strcmp(old, pout) != 0)
				wrote = true;
			free(old);
		} else {
			qm_env_write_atomic(path, pout, &wrote);
			snprintf(path, sizeof(path), "%setc/csh.env", portroot);
			qm_env_write_atomic(path, cout, &wrote);
			snprintf(path, sizeof(path), "%setc/environment.d",
					 portroot);
			mkdir_p(path, 0755);
			snprintf(path, sizeof(path),
					 "%setc/environment.d/10-gentoo-env.conf", portroot);
			qm_env_write_atomic(path, sout, &wrote);
		}
		free(pout);
		free(cout);
		free(sout);
	}

	/* ldconfig -X -r ROOT (Linux), from /, exactly like portage;
	 * -X leaves soname symlinks alone. --no-ldconfig over al, the
	 * env-update equivalent of makelinks=0 mode */
	if (no_ldconfig)
		makelinks = false;
	if (!check_only && makelinks) {
		char ldc[_Q_PATH_MAX];

		snprintf(ldc, sizeof(ldc), "%ssbin/ldconfig", portroot);
		if (access(ldc, X_OK) == 0) {
			char cmd[_Q_PATH_MAX * 2];

			qprintf("%s>>>%s Regenerating %setc/ld.so.cache...\n",
					GREEN, NORM, portroot);
			snprintf(cmd, sizeof(cmd),
					 "cd / && '%s' -X -r '%s'", ldc, portroot);
			if (system(cmd) != 0)
				warn("ldconfig failed");
		}
	}

	array_deepfree(config_list, envd_file_free);
	array_deepfree(env_keys, free);
	array_deepfree(ldpath, free);
	{
		array *ev = hash_values(env);
		char  *evp;

		array_for_each(ev, n, evp)
			free(evp);
		array_free(ev);
		hash_free(env);
	}
	free_set(space_sep);
	free_set(colon_sep);
	if (lib_dirs != NULL)
		free_set(lib_dirs);

	return wrote ? 1 : 0;
}

/* env_update after every package. yay! */
static void
qm_env_update_hook(array *touched)
{
	if (pretend)
		return;
	qm_env_update(false, false, false, touched);
}

/* qmaint env: -c reports stale generated files, -f = env-update CLI */
int
qmerge_env_maint(bool fix, bool no_ldconfig)
{
	int r;

	if (fix) {
		qm_env_update(false, true, no_ldconfig, NULL);
		return 0;
	}
	r = qm_env_update(true, false, no_ldconfig, NULL);
	if (r != 0) {
		warn("generated environment files are stale "
			 "(run `qmaint env -f`)");
		return 1;
	}
	qprintf("%s>>>%s environment files are current\n", GREEN, NORM);
	return 0;
}

/* qmaint moves: emaint-style check/fix for the binhost Moves file,
 * Packages left untouched */
int
qmerge_moves_maint(bool fix)
{
	char    pdir[_Q_PATH_MAX];
	char    mpath[_Q_PATH_MAX + 8];
	char   *want = qm_collect_updates();
	char   *have = NULL;
	size_t  hlen = 0;
	int     ret  = EXIT_SUCCESS;
	int     dfd;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	if (pdir[0] == '/' && pdir[1] == '/')
		memmove(pdir, pdir + 1, strlen(pdir));
	snprintf(mpath, sizeof(mpath), "%s/Moves", pdir);

	dfd = open(pdir, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
	if (fix && dfd < 0) {
		warnp("cannot securely open PKGDIR %s", pdir);
		free(want);
		free(have);
		return EXIT_FAILURE;
	}
	if (dfd >= 0)
		(void)eat_file_at(dfd, "Moves", &have, &hlen);
	else
		(void)eat_file(mpath, &have, &hlen);

	if (fix) {
		if (want != NULL) {
			qm_emit_moves(dfd, pdir);
		} else if (have != NULL) {
			if (unlinkat(dfd, "Moves", 0) == 0)
				qprintf("%s>>>%s removed %s (repo carries no move "
						"directives)\n", GREEN, NORM, mpath);
			else if (errno != ENOENT)
				warnp("cannot remove %s", mpath);
		} else {
			qprintf("%s>>>%s nothing to do (no move directives, no "
					"Moves file)\n", GREEN, NORM);
		}
	} else if (want == NULL && have == NULL) {
		printf("Moves: OK (no move directives, no Moves file)\n");
	} else if (want == NULL) {
		printf("Moves: STALE, %s exists but the repo carries no move "
			   "directives (run `qmaint moves -f')\n", mpath);
		ret = EXIT_FAILURE;
	} else if (have == NULL) {
		printf("Moves: MISSING, the repo carries move directives but "
			   "%s does not exist (run `qmaint moves -f')\n", mpath);
		ret = EXIT_FAILURE;
	} else if (strcmp(want, have) != 0) {
		printf("Moves: OUT OF DATE, %s does not match the repo "
			   "profiles/updates (run `qmaint moves -f')\n", mpath);
		ret = EXIT_FAILURE;
	} else {
		printf("Moves: OK (%zu bytes, matches profiles/updates)\n",
			   strlen(have));
	}
	if (dfd >= 0)
		close(dfd);
	free(want);
	free(have);
	return ret;
}

/* the news item directories under the main repo, NULL-safe */
static set *
qm_news_repo_items(void)
{
	char           ndir[_Q_PATH_MAX];
	DIR           *d;
	struct dirent *de;
	set           *items = create_set();

	if (main_overlay == NULL)
		return items;
	snprintf(ndir, sizeof(ndir), "%s/metadata/news", main_overlay);
	d = opendir(ndir);
	if (d == NULL)
		return items;
	while ((de = readdir(d)) != NULL)
		if (de->d_name[0] != '.')
			add_set_unique(de->d_name, items, NULL);
	closedir(d);
	return items;
}

/* qmaint news: emaint-style check/fix for the binhost News.tar */
int
qmerge_news_maint(bool fix)
{
	char    pdir[_Q_PATH_MAX];
	char    npath[_Q_PATH_MAX + 16];
	set    *want = qm_news_repo_items();
	set    *have = create_set();
	bool    tar_exists;
	struct stat st;
	int     ret = EXIT_SUCCESS;
	int     dfd;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	if (pdir[0] == '/' && pdir[1] == '/')
		memmove(pdir, pdir + 1, strlen(pdir));
	snprintf(npath, sizeof(npath), "%s/News.tar", pdir);

	dfd = open(pdir, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
	if (fix && dfd < 0) {
		warnp("cannot securely open PKGDIR %s", pdir);
		free_set(want);
		free_set(have);
		return EXIT_FAILURE;
	}
	if (dfd >= 0)
		tar_exists = fstatat(dfd, "News.tar", &st, 0) == 0 && st.st_size > 0;
	else
		tar_exists = stat(npath, &st) == 0 && st.st_size > 0;

	if (fix) {
		if (cnt_set(want) > 0) {
			qm_news_force = true;
			qm_emit_news(dfd, pdir);
			qm_news_force = false;
		} else if (tar_exists) {
			if (unlinkat(dfd, "News.tar", 0) == 0)
				qprintf("%s>>>%s removed %s (repo carries no news "
						"items)\n", GREEN, NORM, npath);
			else if (errno != ENOENT)
				warnp("cannot remove %s", npath);
		} else {
			qprintf("%s>>>%s nothing to do (no news items, no "
					"News.tar)\n", GREEN, NORM);
		}
		if (dfd >= 0)
			close(dfd);
		free_set(want);
		free_set(have);
		return EXIT_SUCCESS;
	}

	/* check: item set in the tar vs the repo's news directory */
	if (tar_exists) {
		struct archive       *ar = archive_read_new();
		struct archive_entry *e;

		archive_read_support_format_all(ar);
		if (archive_read_open_filename(ar, npath, 8192) == ARCHIVE_OK) {
			while (archive_read_next_header(ar, &e) == ARCHIVE_OK) {
				const char *p  = archive_entry_pathname(e);
				const char *s1 = p  != NULL ? strchr(p, '/') : NULL;
				const char *s2 = s1 != NULL ? strchr(s1 + 1, '/') : NULL;

				if (s1 != NULL) {
					char item[256];

					snprintf(item, sizeof(item), "%.*s",
							 (int)MIN(s2 != NULL
									  ? (size_t)(s2 - s1 - 1)
									  : strlen(s1 + 1),
									  sizeof(item) - 1),
							 s1 + 1);
					if (item[0] != '\0')
						add_set_unique(item, have, NULL);
				}
				archive_read_data_skip(ar);
			}
		}
		archive_read_free(ar);
	}

	{
		array  *keys;
		size_t  i;
		char   *k;
		int     missing = 0;
		int     stale   = 0;

		keys = set_keys(want);
		array_for_each(keys, i, k)
			if (contains_set(k, have) == NULL) {
				printf("News: item %s missing from %s\n", k, npath);
				missing++;
			}
		array_free(keys);
		keys = set_keys(have);
		array_for_each(keys, i, k)
			if (contains_set(k, want) == NULL) {
				printf("News: stale item %s in %s\n", k, npath);
				stale++;
			}
		array_free(keys);

		if (missing == 0 && stale == 0)
			printf("News: OK (%zu item%s)\n", cnt_set(want),
				   cnt_set(want) == 1 ? "" : "s");
		else {
			printf("News: %d missing, %d stale (run `qmaint news -f')\n",
				   missing, stale);
			ret = EXIT_FAILURE;
		}
	}
	if (dfd >= 0)
		close(dfd);
	free_set(want);
	free_set(have);
	return ret;
}

int
qmerge_binhost_maint(bool fix)
{
	char           pdir[_Q_PATH_MAX];
	char           finp[_Q_PATH_MAX + 16];
	char           gzp[_Q_PATH_MAX + 32];
	array         *ents;
	set           *bypath;
	array         *files;
	array         *errs = array_new();
	struct qbh_pf *f;
	struct qbh_ie *ie;
	struct stat    ist;
	struct stat    gst;
	bool           have_i;
	bool           have_gz;
	size_t         i;
	char          *msg;
	int            ret;

	snprintf(pdir, sizeof(pdir), "%s%s", portroot, pkgdir);
	if (pdir[0] == '/' && pdir[1] == '/')
		memmove(pdir, pdir + 1, strlen(pdir));
	snprintf(finp, sizeof(finp), "%s/%s", pdir, Packages);
	snprintf(gzp, sizeof(gzp), "%.4095s.gz", finp);

	ents  = qbh_load(finp, &bypath);
	files = array_new();
	qbh_quiet_invalid = fix;
	qbh_scan(pdir, files);
	qbh_quiet_invalid = false;
	array_sort(files, qbh_pf_cmp);

	/* emaint: missing (sorted), then stale (index order), then
	 * add the compressed-index consistency errors */
	array_for_each(files, i, f) {
		struct qbh_ie *e = bypath != NULL ?
				(struct qbh_ie *)get_set(f->rel, bypath) : NULL;
		bool ok = e != NULL && e->mtime == f->mtime && e->size == f->size;

		if (ok)
			e->claimed = true;
		if (!ok || !e->has_md5) {
			xasprintf(&msg, "'%s' is not in Packages", f->cpv);
			array_append(errs, msg);
		}
	}
	if (ents != NULL) {
		array_for_each(ents, i, ie) {
			if (ie->claimed)
				continue;
			xasprintf(&msg, "'%s' is not in the repository", ie->cpv);
			array_append(errs, msg);
		}
	}

	have_i  = stat(finp, &ist) == 0;
	have_gz = stat(gzp, &gst) == 0;
	if (!have_i) {
		xasprintf(&msg, "Missing index file: %s", finp);
		array_append(errs, msg);
	}
	if (contains_set("compress-index", features)) {
		if (!have_gz) {
			xasprintf(&msg, "Missing index file: %s", gzp);
			array_append(errs, msg);
		} else if (have_i && ist.st_mtime != gst.st_mtime) {
			xasprintf(&msg, "Uncompressed index timestamp '%lld' is not "
					  "equal to compressed index timestamp '%lld'",
					  (long long)ist.st_mtime, (long long)gst.st_mtime);
			array_append(errs, msg);
		}
	} else if (have_gz) {
		xasprintf(&msg, "Compressed index exists but 'compress-index' "
				  "feature is disabled: %s", gzp);
		array_append(errs, msg);
	}

	if (!fix) {
		/* emaint stlye of print_results framing: blank line, messages, two
		 * blank lines; nothing at all when clean */
		if (array_cnt(errs) > 0) {
			printf("\n");
			array_for_each(errs, i, msg)
				printf("%s\n", msg);
			printf("\n\n");
		}
		ret = array_cnt(errs) > 0 ? EXIT_FAILURE : EXIT_SUCCESS;
	} else if (array_cnt(errs) == 0) {
		ret = EXIT_SUCCESS;
	} else {
		qm_regen_transports = false;
		ret = binpkg_index_regen();
		qm_regen_transports = true;
	}

	array_for_each(errs, i, msg)
		free(msg);
	array_free(errs);
	array_for_each(files, i, f) {
		free(f->rel);
		free(f->cpv);
		free(f);
	}
	array_free(files);
	if (ents != NULL) {
		array_for_each(ents, i, ie) {
			free(ie->cpv);
			free(ie->path);
			free(ie);
		}
		array_free(ents);
	}
	if (bypath != NULL)
		free_set(bypath);
	return ret;
}

static bool
qm_index_trusted(void)
{
	return contains_set("-pkgdir-index-trusted", features) == NULL;
}

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
		} else {
			bool bad;

			if (qm_index_trusted()) {
				char       *szs = tree_pkg_meta(mpkg, Q_SIZE);
				struct stat st;

				bad = szs == NULL || szs[0] == '\0' ||
					fstatat(tree_pkg_get_portroot_fd(mpkg),
							tree_pkg_get_path(mpkg), &st, 0) != 0 ||
					(off_t)strtoull(szs, NULL, 10) != st.st_size;
			} else {
				bad = pkg_verify_checksums(mpkg, 0, 0) != 0;
			}

			if (bad) {
				if (getenv("QMERGE") == NULL)
					unlinkat(tree_pkg_get_portroot_fd(mpkg),
							 tree_pkg_get_path(mpkg), 0);
			} else if (!quiet) {
				/* present and index-valid: reused, NOT re-downloaded.
				 * Emit a per-package line anyway so a full-cache -f
				 * shows steady progress and labels it [cached] so it
				 * can't be mistaken for a re-download. */
				if (qm_dl_total > 0)
					printf(">>> (%zu of %zu) %s [cached]\n",
							qm_dl_n, qm_dl_total, atom_to_string(patom));
				else
					printf(">>> %s [cached]\n", atom_to_string(patom));
				fflush(stdout);
			}
		}
	}

	if (faccessat(tree_pkg_get_portroot_fd(mpkg),
				  tree_pkg_get_path(mpkg), R_OK, 0) != 0)
	{
		char *p;
		char  dest[_Q_PATH_MAX];

		/* only reached when the gpkg is genuinely absent (or was dropped
		 * by -f for a bad checksum), so this line marks a REAL download --
		 * a repeat -f over a valid cache prints nothing here. The
		 * (N of M) counter comes from the prefetch pool, or from the
		 * merge pass on the sequential path.  -q keeps exactly this one
		 * line per package, tagged with the source repo, and nothing
		 * else. */
		if (quiet) {
			size_t      n  = qm_dl_total > 0 ? qm_dl_n : qm_mg_n;
			size_t      t  = qm_dl_total > 0 ? qm_dl_total : qm_mg_total;
			const char *rn = qm_repo_name_of_pkg(mpkg);

			if (t > 0)
				printf("Fetching package (%zu of %zu) %s%s%s\n",
						n, t, atom_to_string(patom),
						rn != NULL ? " from " : "",
						rn != NULL ? rn : "");
			else
				printf("Fetching package %s%s%s\n",
						atom_to_string(patom),
						rn != NULL ? " from " : "",
						rn != NULL ? rn : "");
			fflush(stdout);
		} else {
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

		p = q_deconst(binpkg_relpath_loc(p, loc));
		{
			const char *sl   = strrchr(p, '/');
			size_t      plen = sl == NULL ? 0 : (size_t)(sl - p);
			size_t      rl   = strlen(portroot);
			size_t      ll   = strlen(loc);
			size_t      off;

			if (rl >= sizeof(dest) || ll >= sizeof(dest) ||
					plen >= sizeof(dest) ||
					rl + ll + (plen > 0 ? 1 : 0) + plen >= sizeof(dest))
			{
				warn("binpkg path too long for %s, skipping",
					 atom_to_string(patom));
				return false;
			}
			memcpy(dest, portroot, rl);
			off = rl;
			memcpy(dest + off, loc, ll);
			off += ll;
			if (plen > 0)
				dest[off++] = '/';
			memcpy(dest + off, p, plen);
			off += plen;
			dest[off] = '\0';
		}
		if (mkdir_p(dest, 0755) != 0)
		{
			warnp("Failed to create %s", dest);
			return false;
		}
		binpkg_tree_perms(dest);

		/* route to the repo that advertised this pkg; only when that
		 * fails scan the full fallback order */
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
	if (qmerge_processed_pkgs != NULL &&
			contains_set(pkg_key, qmerge_processed_pkgs) != NULL) {
		IF_DEBUG(fprintf(stderr, "  skipping already queued %s\n", pkg_key));
		return;
	}
	if (qmerge_processed_pkgs == NULL)
		qmerge_processed_pkgs = create_set();
	add_set(pkg_key, qmerge_processed_pkgs);

	/* -F if they're not forced, they're like before.
	 * if they're forced, we skip the regular soft checks.
	 * this is the best we could do here. */
	bool forced = qm_force_soft() && qm_force_targets != NULL &&
			contains_set(pkg_key, qm_force_targets) != NULL;

	/* package.mask visibility checks (backstop; selection already filters) */
	if (!forced && binpkg_masked(patom)) {
		warn("%s is masked by package.mask -- refusing (unmask to override)",
			 atom_to_string(patom));
		qm_exec_fail(patom);
		return;
	}

	/* GLEP 53: keyword visibility check, before fetching or merging */
	if (!forced && !binpkg_keywords_ok(mpkg, patom, false)) {
		qm_exec_fail(patom);
		return;
	}

	/* GLEP 23: license visibility checks */
	if (!forced && !binpkg_license_ok(mpkg, patom, false)) {
		qm_exec_fail(patom);
		return;
	}

	/* --usepkg-exclude backstop (selection already filters) */
	if (!forced && binpkg_excluded(mpkg, patom, false)) {
		qm_exec_fail(patom);
		return;
	}

	/* qmerge -pv patch */
	if (pretend) {
		if (!install)
			install++;
		pkg_merge(level, qatom, mpkg);
		return;
	}

	/* download into PKGDIR (a no-op when a parallel prefetch already
	 * pulled it, or when the package is otherwise present). */
	bool was_present = faccessat(tree_pkg_get_portroot_fd(mpkg),
								 tree_pkg_get_path(mpkg), R_OK, 0) == 0;
	if (!pkg_download(mpkg)) {
		qm_exec_fail(patom);
		return;
	}

	verifyret = pkg_verify_checksums(mpkg, qmerge_strict, !quiet);
	if (verifyret == -1) {
		warn("No checksum data for %s (try `emaint binhost --fix`)",
				tree_pkg_get_path(mpkg));
		qm_exec_fail(patom);
		return;
	} else if (verifyret == 0) {
		pkg_merge(0, qatom, mpkg);
		return;
	} else {
		int         rfd  = tree_pkg_get_portroot_fd(mpkg);
		const char *path = tree_pkg_get_path(mpkg);
		char        aside[_Q_PATH_MAX + 32];
		bool        moved;

		snprintf(aside, sizeof(aside), "%s.checksum_failure", path);
		warn("checksum mismatch for %s, moving aside to %s and "
				"refetching", path, aside);
		moved = renameat(rfd, path, rfd, aside) == 0;
		if (!pkg_download(mpkg)) {
			qm_exec_fail(patom);
			return;
		}
		verifyret = pkg_verify_checksums(mpkg, qmerge_strict, !quiet);
		if (verifyret == 0) {
			pkg_merge(0, qatom, mpkg);
			return;
		}
		warn("checksum mismatch persists for %s after refetch, refusing "
				"to merge (corrupt or tampered binhost)", path);
		if (moved || !was_present)
			(void)unlinkat(rfd, path, 0);
		qm_exec_fail(patom);
		return;
	}
}

/* Workaround: pull this in, knowing that qlist will be in the final link, we
 * should however figure out how to do what match does here from e.g.
 * atom FIXME use tree_match_atom instead */
extern bool qlist_match(
		tree_pkg_ctx *pkg_ctx,
		const char *name,
		depend_atom **name_atom,
		bool exact,
		bool applymasks);

struct qm_keepscan {
	set        *keep;
	const char *skip_cat;
	const char *skip_pf;
};

static int
/* we either write full docs, or we don't write at all.
 * one line with 16 random characters won't help anyone understand
 * wtf is going on in that line. */
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
		return 0;

	contents = tree_pkg_meta(pkg_ctx, Q_CONTENTS);
	if (contents == NULL)
		return 0;
	contents = xstrdup(contents);

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
 * packages OTHER than skip_cat/skip_pf.
 * Passed to pkg_unmerge as its keep set so a standalone unmerge
 * never deletes a file another package still owns, Portage
 * gives the same protection via others_in_slot. */
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
			atom_ctx *a    = tree_pkg_atom(pkg_ctx, true);
			set      *keep = uninstall_force
					? create_set()
					: qm_other_owned_files(a->CATEGORY, a->PF);
			array    *pres = NULL;
			char      uslot[128];
			char      ucnt[64];
			char      ucpv[512];

			snprintf(uslot, sizeof(uslot), "%s", a->SLOT ? : "0");
			snprintf(ucpv, sizeof(ucpv), "%s/%s",
					 a->CATEGORY ? : "", a->PF ? : "");
			ucnt[0] = '\0';
			{
				char   cpath[_Q_PATH_MAX];
				char  *cbuf = NULL;
				size_t clen = 0;

				snprintf(cpath, sizeof(cpath), "%s%s/%s/%s/COUNTER",
						 portroot, portvdb,
						 a->CATEGORY ? : "", a->PF ? : "");
				if (eat_file(cpath, &cbuf, &clen) && cbuf != NULL)
					snprintf(ucnt, sizeof(ucnt), "%s", cbuf);
				free(cbuf);
			}
			if (!pretend && !uninstall_force && qm_preserve_active()) {
				array *one = array_new();

				array_append(one, pkg_ctx);
				pres = qm_preserve_compute(one, NULL, keep);
				array_free(one);
			}
			pkg_unmerge(pkg_ctx, NULL, keep,
					cp_argc, cp_argv, cpm_argc, cpm_argv);
			free_set(keep);
			if (!pretend) {
				preserved_unregister(qm_preserved_get(), ucpv,
									 uslot, ucnt);
				if (pres != NULL)
					preserved_register(qm_preserved_get(), ucpv,
									   uslot, ucnt, pres);
			}
			if (pres != NULL)
				array_deepfree(pres, free);
			if (!pretend && a->CATEGORY != NULL && a->PN != NULL) {
				char cp[_Q_PATH_MAX];

				snprintf(cp, sizeof(cp), "%s/%s", a->CATEGORY, a->PN);
				qm_unmerged_cps =
						add_set_unique(cp, qm_unmerged_cps, NULL);
			}
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
	if (!pretend) {
		qm_preserved_gc();
		qm_preserved_finish();
	}
	if (!pretend && qm_deselect != 0)
		qm_world_clean_unmerged();
	return ret;
}

/* this is where we'll have @sets files, and their expansion */
static set *qmerge_expand_setname(const char *name, set *q);

static set *qm_sets_seen = NULL;

static set *
qmerge_expand_setref(const char *name, set *q)
{
	bool ok;

	if (contains_set(name, qm_sets_seen) != NULL) {
		warn("circular set reference: @%s (skipped)", name);
		return q;
	}
	qm_sets_seen = add_set_unique(name, qm_sets_seen, NULL);
	q = qmerge_expand_setname(name, q);
	(void)del_set(name, qm_sets_seen, &ok);
	return q;
}

/* one set-file token: @name recurses, anything else is an atom */
static set *
qmerge_add_set_token(char *tok, set *q)
{
	if (tok[0] == '\0' || tok[0] == '#')
		return q;
	if (tok[0] == '@' && tok[1] != '\0')
		return qmerge_expand_setref(tok + 1, q);
	return add_set_unique(tok, q, NULL);
}

static set *
qmerge_add_set_file(const char *pfx, const char *dir, const char *file,
					bool optional, set *q)
{
	FILE *fp;
	int linelen;
	size_t buflen;
	char *buf, *fname;

	xasprintf(&fname, "%s%s%s/%s", portroot, pfx, dir, file);

	if ((fp = fopen(fname, "r")) == NULL) {
		if (!optional || errno != ENOENT)
			warnp("unable to read set file %s", fname);
		free(fname);
		return q;
	}
	free(fname);

	buf = NULL;
	while ((linelen = getline(&buf, &buflen, fp)) >= 0) {
		char *sp;

		rmspace_len(buf, (size_t)linelen);
		for (sp = buf; *sp != '\0' && *sp != ' ' && *sp != '\t'; sp++)
			;
		*sp = '\0';
		q = qmerge_add_set_token(buf, q);
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
	atom_ctx *a = tree_pkg_atom(pkg, true);
	char      cpn[512];

	if (a == NULL || a->CATEGORY == NULL || a->PN == NULL)
		return 0;
	/* multi-slot packages must contribute one member per slot.
	 * so we enforce them to not collapse per slor */
	if (a->SLOT != NULL && a->SLOT[0] != '\0')
		snprintf(cpn, sizeof(cpn), "%s/%s:%s", a->CATEGORY, a->PN, a->SLOT);
	else
		snprintf(cpn, sizeof(cpn), "%s/%s", a->CATEGORY, a->PN);
	*q = add_set_unique(cpn, *q, NULL);
	return 0;
}

/* DDD: note, this doesn't handle the class-based sets from portage's
 *      sets.conf (module-rebuild, security, ...); builtins + file sets
 *      cover the binhost-eater surface */
/* is @profile enabled? portage gates per profile node on profile-set
 * in the repo's metadata/layout.conf profile-formats.
 * We approximate with the repo owning the make.profile 
 * symlink target (standard gentoo repos do not declare it, 
 * so the set is empty there) */
static bool
qm_profile_set_enabled(void)
{
	char    lnk[_Q_PATH_MAX];
	char    dir[_Q_PATH_MAX * 2];
	char    lc[_Q_PATH_MAX * 2 + 32];
	ssize_t n;
	char   *s;

	n = readlink(CONFIG_EPREFIX "etc/portage/make.profile",
				 lnk, sizeof(lnk) - 1);
	if (n < 0)
		n = readlink(CONFIG_EPREFIX "etc/make.profile",
					 lnk, sizeof(lnk) - 1);
	if (n < 0)
		return false;
	lnk[n] = '\0';

	if (lnk[0] == '/')
		snprintf(dir, sizeof(dir), "%s", lnk);
	else
		snprintf(dir, sizeof(dir), CONFIG_EPREFIX "etc/portage/%s", lnk);

	/* ascend to the repo root's metadata/layout.conf */
	while (1) {
		char   *buf = NULL;
		size_t  len = 0;

		snprintf(lc, sizeof(lc), "%.4095s/metadata/layout.conf", dir);
		if (eat_file(lc, &buf, &len) && buf != NULL) {
			bool  ret = false;
			char *sp;

			for (s = strtok_r(buf, "\r\n", &sp); s != NULL;
				 s = strtok_r(NULL, "\r\n", &sp))
			{
				while (*s == ' ' || *s == '\t')
					s++;
				if (strncmp(s, "profile-formats", 15) == 0 &&
						strstr(s, "profile-set") != NULL) {
					ret = true;
					break;
				}
			}
			free(buf);
			return ret;
		}
		free(buf);
		s = strrchr(dir, '/');
		if (s == NULL || s == dir)
			return false;
		*s = '\0';
	}
}

/* profile packages non-star entries = portage's @profile set
 * (ProfilePackageSet); -atom removes an earlier entry */
static void *
qmerge_add_set_profile(void *data, char *buf)
{
	set  *q = data;
	char *s;

	s = strchr(buf, '#');
	if (s)
		*s = '\0';
	rmspace(buf);

	if (buf[0] == '\0' || buf[0] == '*')
		return q;
	if (buf[0] == '-') {
		bool ok;

		if (buf[1] != '*')
			(void)del_set(buf + 1, q, &ok);
		return q;
	}
	return add_set(buf, q);
}

/* expand one known set name (leading @ removed) into q; builtin
 * composition mirrors portage cnf/sets/portage.conf */
static set *
qmerge_expand_setname(const char *name, set *q)
{
	/* world = profile + selected + system. portage style. */
	if (strcmp(name, "world") == 0) {
		q = qmerge_expand_setref("profile", q);
		q = qmerge_expand_setref("selected", q);
		return qmerge_expand_setref("system", q);
	}
	/* selected = the world file plus the world_sets set refs */
	if (strcmp(name, "selected") == 0) {
		q = qmerge_expand_setref("selected-packages", q);
		return qmerge_expand_setref("selected-sets", q);
	}
	if (strcmp(name, "selected-packages") == 0)
		return qmerge_add_set_file(CONFIG_EPREFIX, "/var/lib/portage",
								   "world", true, q);
	if (strcmp(name, "selected-sets") == 0)
		return qmerge_add_set_file(CONFIG_EPREFIX, "/var/lib/portage",
								   "world_sets", true, q);
	if (strcmp(name, "all") == 0 || strcmp(name, "installed") == 0) {
		/* every installed package as cat/pn:slot (portage's
		 * EverythingSet emits slot atoms), via a plain VDB enumeration --
		 * tree_match_atom has no match-all query */
		tree_ctx *ctx = tree_new(portroot, portvdb, TREETYPE_VDB, true);

		if (ctx != NULL) {
			tree_foreach_pkg_fast(ctx, qmerge_all_cb, &q, NULL);
			tree_close(ctx);
		}
		return q;
	}
	if (strcmp(name, "system") == 0) {
		size_t before = q != NULL ? cnt_set(q) : 0;

		q = q_profile_follow("packages", qmerge_add_set_system, q);
		if ((q != NULL ? cnt_set(q) : 0) == before)
			warn("@system is empty: no profile packages found "
				 "(no profile configured?)");
		return q;
	}
	if (strcmp(name, "profile") == 0) {
		if (!qm_profile_set_enabled())
			return q;
		return q_profile_follow("packages", qmerge_add_set_profile, q);
	}
	/* revdep packages still NEEDing a preserved library.
	 * a revdep whose only candidate build still links the preserved soname
	 * is held out of the set.
	 * (if you re-merge it changes nothing until the binhost carries a rebuilt one)
	 * above scenario is consacrated as best scenario for good remote binhost management. */
	if (strcmp(name, "preserved-rebuild") == 0) {
		preserved_reg *reg = qm_preserved_get();
		linkage_map   *map;
		set           *cand = NULL;
		array         *ck;
		size_t         i;
		char          *cc;
		preserved_entry *pe;

		if (preserved_count(reg) == 0)
			return q;
		map = qm_linkage_build();
		array_for_each(preserved_entries(reg), i, pe) {
			size_t n;
			char  *pt;

			array_for_each(pe->paths, n, pt) {
				const char *bn = strrchr(pt, '/');
				array      *cons;
				size_t      ci;
				char       *cv;

				bn   = bn != NULL ? bn + 1 : pt;
				cons = linkage_revdeps(map, NULL, bn, NULL);
				array_for_each(cons, ci, cv)
					cand = add_set_unique(cv, cand, NULL);
				array_deepfree(cons, free);
			}
		}
		linkage_free(map);
		ck = set_keys(cand);
		array_for_each(ck, i, cc) {
			atom_ctx     *ca = atom_explode(cc);
			atom_ctx     *cna;
			tree_pkg_ctx *bin;
			char          cpn[512];
			bool          held = true;

			if (ca == NULL)
				continue;
			snprintf(cpn, sizeof(cpn), "%s/%s",
					 ca->CATEGORY ? : "", ca->PN ? : "");
			cna = atom_explode(cpn);
			bin = cna != NULL ? best_version(cna, BV_BINPKG) : NULL;
			if (bin != NULL) {
				char *req = tree_pkg_meta(bin, Q_REQUIRES);

				held = false;
				if (req != NULL) {
					size_t           ei;
					preserved_entry *ee;

					array_for_each(preserved_entries(reg), ei, ee) {
						size_t pn2;
						char  *pt2;

						array_for_each(ee->paths, pn2, pt2) {
							const char *bn2 = strrchr(pt2, '/');

							bn2 = bn2 != NULL ? bn2 + 1 : pt2;
							if (qm_soname_in(req, NULL, bn2)) {
								held = true;
								break;
							}
						}
						if (held)
							break;
					}
				}
			}
			if (!held)
				q = add_set_unique(cpn, q, NULL);
			else if (verbose)
				warn("@preserved-rebuild: holding %s (%s)", cpn,
					 bin == NULL ? "no binpkg candidate" :
					 "binhost build still links a preserved library");
			if (cna != NULL)
				atom_implode(cna);
			atom_implode(ca);
		}
		array_free(ck);
		if (cand != NULL)
			free_set(cand);
		return q;
	}
	/* TODO: use configroot */
	return qmerge_add_set_file(CONFIG_EPREFIX,
							   "/etc/portage/sets", name, false, q);
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

/* -s: search over the binhost Packages catalog. Read-only (index
 * only) never opens a .gpkg, so it works on a fresh box that has only
 * fetched the index via qmerge -f and not downloaded any package yet.
 * Plain searches are regexes on cat/pn and pn (--exact for precision),
 * keys carrying a pkgversion, slot or operator match as atoms against
 * every catalog instance, bare name-ver will point to =name-ver*. */
static bool qm_search_exact = false;

struct qm_search_state {
	regex_t      *res;
	depend_atom **atoms;
	int           npat;
	set          *cpns;
};

/* ffsearch atoms */
static depend_atom *
qm_search_atom_key(const char *pat)
{
	const char  *p;
	depend_atom *a;

	for (p = pat; *p != '\0'; p++) {
		if (isalnum((unsigned char)*p) ||
				strchr("+_-/:@.~=<>", *p) != NULL ||
				(*p == '*' && p[1] == '\0'))
			continue;
		return NULL;
	}

	a = atom_explode(pat);
	if (a == NULL)
		return NULL;
	if (a->PN == NULL ||
			(a->PVR == NULL && a->SLOT == NULL &&
			 a->pfx_op == ATOM_OP_NONE))
	{
		atom_implode(a);
		return NULL;
	}
	if (a->pfx_op == ATOM_OP_NONE && a->PVR != NULL) {
		a->pfx_op = ATOM_OP_EQUAL;
		if (a->sfx_op == ATOM_OP_NONE)
			a->sfx_op = ATOM_OP_STAR;
	}
	a->REPO = NULL;
	return a;
}

static int
qm_search_cb(tree_pkg_ctx *pkg, void *priv)
{
	struct qm_search_state *st   = priv;
	depend_atom            *atom = tree_pkg_atom(pkg, false);
	depend_atom            *hit  = NULL;
	char                    cpn[_Q_PATH_MAX];
	int                     i;
	bool                    match;

	if (atom == NULL || atom->CATEGORY == NULL || atom->PN == NULL)
		return 0;

	/* plain string, NOT atom_format: that embeds ANSI color codes when
	 * stdout is a tty, which breaks both regexec and the set keys */
	snprintf(cpn, sizeof(cpn), "%s/%s", atom->CATEGORY, atom->PN);

	if (st->npat == 0) {
		match = true;
	} else {
		match = false;
		for (i = 0; i < st->npat; i++) {
			if (st->atoms[i] != NULL) {
				depend_atom *pa = tree_pkg_atom(pkg, true);

				if (pa != NULL &&
						atom_compare(pa, st->atoms[i]) == EQUAL)
				{
					match = true;
					hit   = st->atoms[i];
				}
			} else if (regexec(&st->res[i], cpn, 0, NULL, 0) == 0 ||
					regexec(&st->res[i], atom->PN, 0, NULL, 0) == 0) {
				match = true;
			}
			if (match)
				break;
		}
	}


	if (match) {
		if (st->cpns == NULL)
			st->cpns = hash_new();
		if (hash_get(st->cpns, cpn) == NULL)
			hash_add(st->cpns, cpn, hit, NULL);
	}

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

	bu = usedep_flags_to_set(tree_pkg_meta(bv, Q_USE));
	if (iv != NULL) {
		iu      = usedep_flags_to_set(tree_pkg_meta(iv, Q_USE));
		oldiuse = usedep_flags_to_set(tree_pkg_meta(iv, Q_IUSE));
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

		/* introducing repo-agnostic classification when someone builds
		 * packages on local PKGDIR, we need proper label for this.
		 * todo: documentation by @francoisb */
		switch (atom_compare_flg(ba, ia,
					ATOM_COMP_NOSUBSLOT | ATOM_COMP_NOREPO)) {
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
				if (ol < sizeof(oldv) - 2)
					snprintf(oldv + ol, sizeof(oldv) - ol,
							 ":%s", ia->SLOT);
			}
			{
				size_t ol = strlen(oldv);
				if (ol < sizeof(oldv) - 2)
					snprintf(oldv + ol, sizeof(oldv) - ol,
							 "]%s", NORM);
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
	regex_t                *res    = NULL;
	depend_atom           **qatoms = NULL;
	array                  *keys;
	size_t                  n;
	size_t                  ri;
	size_t                  rcnt = qm_bintree_cnt();
	bool                    anytree = false;
	char                   *cpn;
	int                     i;
	int                     found = 0;
	int                     insts = 0;

	for (ri = 0; ri < rcnt; ri++)
		if (qm_bintree(ri) != NULL)
			anytree = true;
	if (!anytree) {
		warn("no binary package index found; run `qmerge -f' first");
		return EXIT_FAILURE;
	}

	if (npat > 0) {
		res    = xmalloc(sizeof(*res) * npat);
		qatoms = xmalloc(sizeof(*qatoms) * npat);
		for (i = 0; i < npat; i++) {
			int r;

			qatoms[i] = qm_search_atom_key(pats[i]);
			if (qatoms[i] != NULL)
				continue;
			if (qm_search_exact) {
				char *ap;

				xasprintf(&ap, "^(%s)$", pats[i]);
				r = regcomp(&res[i], ap,
							REG_EXTENDED | REG_ICASE | REG_NOSUB);
				free(ap);
			} else {
				r = regcomp(&res[i], pats[i],
							REG_EXTENDED | REG_ICASE | REG_NOSUB);
			}
			if (r != 0) {
				char eb[256];
				regerror(r, &res[i], eb, sizeof(eb));
				warn("invalid search pattern `%s': %s", pats[i], eb);
				while (i-- > 0) {
					if (qatoms[i] != NULL)
						atom_implode(qatoms[i]);
					else
						regfree(&res[i]);
				}
				free(res);
				free(qatoms);
				return EXIT_FAILURE;
			}
		}
	}

	st.res   = res;
	st.atoms = qatoms;
	st.npat  = npat;
	st.cpns  = NULL;

	/* collect names across every repo's catalog (trees sharing a store
	 * were deduped to the same pointer; skip repeats) */
	for (ri = 0; ri < rcnt; ri++) {
		tree_ctx *bt = qm_bintree(ri);
		size_t    rj;
		bool      seen = false;

		if (bt == NULL)
			continue;
		if (qm_binrepos[ri].priority == 0)
			/* emergency store: explicit @reponame only.
			 * we have to make it clear that @reponame is the standaard,
			 * if we want to install from other sources
			 * even from emergency */
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
			depend_atom  *a  = atom_explode(cpn);
			depend_atom  *qa = get_set(cpn, st.cpns);
			depend_atom  *ma = a;
			tree_pkg_ctx *bv;
			tree_pkg_ctx *iv;

			if (a == NULL)
				continue;

			if (qa != NULL) {
				char mbuf[_Q_PATH_MAX + 64];

				snprintf(mbuf, sizeof(mbuf), "%s%s%s%s%s%s%s%s%s",
						 atom_op_str[qa->pfx_op], cpn,
						 qa->PVR != NULL ? "-" : "",
						 qa->PVR != NULL ? qa->PVR : "",
						 qa->sfx_op == ATOM_OP_STAR ? "*" : "",
						 qa->SLOT != NULL ? ":" : "",
						 qa->SLOT != NULL ? qa->SLOT : "",
						 qa->SUBSLOT != NULL ? "/" : "",
						 qa->SUBSLOT != NULL ? qa->SUBSLOT : "");
				ma = atom_explode(mbuf);
				if (ma == NULL)
					ma = a;
			}

			/* -vv: raw catalog view, every version and build instance
			 * in every repo, no installability gates. What EXISTS on
			 * the binhosts in praktice. */
			if (verbose > 1) {
				size_t vrcnt = qm_bintree_cnt();
				size_t vri;

				iv = best_version(a, BV_VDB);
				for (vri = 0; vri < vrcnt; vri++) {
					tree_ctx     *bt = qm_bintree(vri);
					array        *t;
					size_t        cn;
					tree_pkg_ctx *cand;
					size_t        rj;
					bool          seen = false;

					if (bt == NULL)
						continue;
					if (qm_nbinrepos > 0 &&
							qm_binrepos[vri].priority == 0)
						continue;
					for (rj = 0; rj < vri; rj++)
						if (qm_bintrees[rj] == bt)
							seen = true;
					if (seen)
						continue;
					t = tree_match_atom(bt, ma,
							TREE_MATCH_SORT | TREE_MATCH_VIRTUAL |
							TREE_MATCH_ACCT);
					array_for_each(t, cn, cand) {
						qm_search_print_line(cpn, cand, iv, NULL);
						insts++;
					}
					array_free(t);
				}
				found++;
				if (ma != a)
					atom_implode(ma);
				atom_implode(a);
				continue;
			}

			/* best_version applies the same mask/keyword/license gates
			 * the resolver uses, so results == what qmerge could merge;
			 * -v also lists names with no currently installable binpkg */
			bv = best_version(ma, BV_BINPKG);
			if (bv == NULL && !verbose) {
				if (ma != a)
					atom_implode(ma);
				atom_implode(a);
				continue;
			}
			iv = best_version(a, BV_VDB);

			/* emerge -pvK line format:
			 * [binary   R    ] cat/pn-PVR-BID:SLOT/SUB::repo [old] SIZE KiB
			 * the verbose mode can only be reached with -v */
			if (bv == NULL) {
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
						if (qm_binrepos[vri].priority == 0)
							continue;
						bt = qm_bintree(vri);
						if (bt == NULL ||
								(w >= 0 && qm_bintrees[w] == bt))
							continue;

						t = tree_match_atom(bt, ma,
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
												qm_respect_use == 1,
												why, sizeof(why));
							}
							break;
						}
						array_free(t);

						if (rbest == NULL)
							continue;
						qm_search_print_line(cpn, rbest, iv,
								usebad ? "(USE mismatch)" :
								w >= 0 && qm_repo_pos(vri) >
										qm_repo_pos((size_t)w) ?
								"(not selected: lower priority)" :
								"(not selected: older than installed)");
					}
				}
			}
			found++;
			if (ma != a)
				atom_implode(ma);
			atom_implode(a);
		}
		array_free(keys);
	}

	if (res != NULL) {
		for (i = 0; i < npat; i++) {
			if (qatoms[i] != NULL)
				atom_implode(qatoms[i]);
			else
				regfree(&res[i]);
		}
		free(res);
		free(qatoms);
	}
	if (st.cpns != NULL)
		free_set(st.cpns);

	if (found == 0)
		warn("no matching packages in the binhost index");
	else if (verbose > 1)
		printf("\n%sTotal:%s %d package name%s, %d binpkg instance%s\n",
			   BOLD, NORM, found, found == 1 ? "" : "s",
			   insts, insts == 1 ? "" : "s");
	else if (verbose)
		printf("\n%sTotal:%s %d package name%s\n",
			   BOLD, NORM, found, found == 1 ? "" : "s");

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
			 * the resulting merge list in dependency order */
			return qm_resolve_and_merge(todo);
		}
	}
}

/* portage --jobs grammar: n=serial, y/True=unlimited (capped), 0=one per
 * CPU, N=that many.
 * Shared by the -j flag and $QMERGE_JOBS. */
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

/* this is where oneshot | -1 feature has been added
 to be documented by @francoisb */
static set *qm_world_select    = NULL;
static set *qm_worldset_select = NULL;

static bool
qm_setname_builtin(const char *n)
{
	return strcmp(n, "world") == 0 || strcmp(n, "system") == 0 ||
		   strcmp(n, "all") == 0 || strcmp(n, "installed") == 0 ||
		   strcmp(n, "profile") == 0 || strcmp(n, "selected") == 0 ||
		   strcmp(n, "selected-packages") == 0 ||
		   strcmp(n, "selected-sets") == 0;
}

static void
qm_world_capture(const char *arg)
{
	char *buf = xstrdup(arg);

	rmspace(buf);
	if (buf[0] == '@') {
		char *pin = strchr(buf + 1, '@');

		if (pin != NULL)
			*pin = '\0';
		if (buf[1] != '\0' && !qm_setname_builtin(buf + 1))
			qm_worldset_select =
					add_set_unique(buf, qm_worldset_select, NULL);
	} else if (buf[0] != '\0' &&
			strcmp(buf, "world") != 0 && strcmp(buf, "all") != 0 &&
			strcmp(buf, "system") != 0)
		qm_world_select = add_set_unique(buf, qm_world_select, NULL);
	free(buf);
}

static char *
qm_world_atom(const char *arg)
{
	char        *tmp = xstrdup(arg);
	char        *cc;
	depend_atom *a;
	const char  *cat;
	char        *picked = NULL;
	char        *ret    = NULL;

	cc = strchr(tmp, '@');
	if (cc != NULL)
		*cc = '\0';
	cc = strstr(tmp, "::");
	if (cc != NULL)
		*cc = '\0';

	a = atom_explode(tmp);
	free(tmp);
	if (a == NULL)
		return NULL;

	cat = a->CATEGORY;
	if (cat == NULL && a->PN != NULL) {
		bool amb = false;

		picked = qm_pick_category(a->PN, &amb, NULL);
		cat = picked;
	}
	if (cat != NULL && a->PN != NULL) {
		if (a->SLOT != NULL)
			xasprintf(&ret, "%s/%s:%s", cat, a->PN, a->SLOT);
		else
			xasprintf(&ret, "%s/%s", cat, a->PN);
	}
	atom_implode(a);
	free(picked);
	return ret;
}

/* note that world_update refers to world file update here
  to be documented by @francoisb */
static void
qm_world_update(void)
{
	char   *wdir;
	char   *wpath;
	char   *buf   = NULL;
	size_t  len   = 0;
	set    *entries;
	array  *keys;
	size_t  n;
	char   *k;
	int     added = 0;

	if (qm_world_select == NULL || cnt_set(qm_world_select) == 0)
		return;

	xasprintf(&wdir, "%s%s/var/lib/portage", portroot, CONFIG_EPREFIX);
	xasprintf(&wpath, "%s/world", wdir);

	entries = create_set();
	if (eat_file(wpath, &buf, &len) && buf != NULL) {
		char *line;
		char *sp;

		for (line = strtok_r(buf, "\r\n", &sp);
			 line != NULL;
			 line = strtok_r(NULL, "\r\n", &sp))
		{
			char *t = rmspace(line);

			if (*t != '\0' && *t != '#')
				add_set_unique(t, entries, NULL);
		}
	}
	free(buf);

	/* establish the world installed as selections only. 
	 * a fresh vdb tree, the resolver's cached one predates 
	  * the merges of this very run. */
	{
		tree_ctx *vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);

		keys = set_keys(qm_world_select);
		array_for_each(keys, n, k) {
			char *wa = qm_world_atom(k);

			if (wa == NULL)
				continue;
			if (vdb != NULL) {
				atom_ctx *va   = atom_explode(wa);
				bool      inst = false;

				if (va != NULL) {
					array *t = tree_match_atom(vdb, va,
							TREE_MATCH_LATEST  | TREE_MATCH_FIRST |
							TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);

					inst = array_cnt(t) > 0;
					array_free(t);
					atom_implode(va);
				}
				if (!inst) {
					free(wa);
					continue;
				}
			}
			if (contains_set(wa, entries) == NULL) {
				add_set_unique(wa, entries, NULL);
				qprintf("%s>>>%s Recording %s in \"world\" favorites "
						"file\n", GREEN, NORM, wa);
				added++;
			}
			free(wa);
		}
		array_free(keys);
		if (vdb != NULL)
			tree_close(vdb);
	}

	if (added > 0) {
		array *ek = set_keys(entries);
		char  *tmp;
		FILE  *f;

		array_sort(ek, qm_strcmp_cb);
		mkdir_p(wdir, 0755);
		xasprintf(&tmp, "%s.qmerge.%d", wpath, (int)getpid());
		f = fopen(tmp, "w");
		if (f != NULL) {
			size_t m;
			char  *e;
			bool   ok = true;

			array_for_each(ek, m, e)
				if (fprintf(f, "%s\n", e) < 0)
					ok = false;
			if (fclose(f) != 0)
				ok = false;
			if (!ok) {
				warnp("could not write world file %s", wpath);
				unlink(tmp);
			} else if (rename(tmp, wpath) != 0) {
				warnp("could not update world file %s", wpath);
				unlink(tmp);
			}
		} else {
			warnp("could not write %s", tmp);
		}
		free(tmp);
		array_free(ek);
	}

	free_set(entries);
	free(wpath);
	free(wdir);
}

/* record installed user-set NAMES in world_sets (!), the set counterpart
 * of qm_world_update. non-destructive && sorted && atomic */
static void
qm_worldsets_update(void)
{
	char   *wdir;
	char   *wpath;
	char   *buf   = NULL;
	size_t  len   = 0;
	set    *entries;
	array  *keys;
	size_t  n;
	char   *k;
	int     added = 0;

	if (qm_worldset_select == NULL || cnt_set(qm_worldset_select) == 0)
		return;

	xasprintf(&wdir, "%s%s/var/lib/portage", portroot, CONFIG_EPREFIX);
	xasprintf(&wpath, "%s/world_sets", wdir);

	entries = create_set();
	if (eat_file(wpath, &buf, &len) && buf != NULL) {
		char *line;
		char *sp;

		for (line = strtok_r(buf, "\r\n", &sp);
			 line != NULL;
			 line = strtok_r(NULL, "\r\n", &sp))
		{
			char *t = rmspace(line);

			if (*t == '@')
				add_set_unique(t, entries, NULL);
		}
	}
	free(buf);

	keys = set_keys(qm_worldset_select);
	array_for_each(keys, n, k) {
		if (contains_set(k, entries) == NULL) {
			add_set_unique(k, entries, NULL);
			qprintf("%s>>>%s Recording %s in \"world_sets\" file\n",
					GREEN, NORM, k);
			added++;
		}
	}
	array_free(keys);

	if (added > 0) {
		array *ek = set_keys(entries);
		char  *tmp;
		FILE  *f;

		array_sort(ek, qm_strcmp_cb);
		mkdir_p(wdir, 0755);
		xasprintf(&tmp, "%s.qmerge.%d", wpath, (int)getpid());
		f = fopen(tmp, "w");
		if (f != NULL) {
			size_t m;
			char  *e;
			bool   ok = true;

			array_for_each(ek, m, e)
				if (fprintf(f, "%s\n", e) < 0)
					ok = false;
			if (fclose(f) != 0)
				ok = false;
			if (!ok) {
				warnp("could not write world_sets file %s", wpath);
				unlink(tmp);
			} else if (rename(tmp, wpath) != 0) {
				warnp("could not update world_sets file %s", wpath);
				unlink(tmp);
			}
		} else {
			warnp("could not write %s", tmp);
		}
		free(tmp);
		array_free(ek);
	}

	free_set(entries);
	free(wpath);
	free(wdir);
}

/* rewrite the world (or world_sets) file without the entries in
 * `drop`*/
static void
qm_world_rewrite(const char *fname, set *keepset)
{
	char  *wdir;
	char  *wpath;
	char  *tmp;
	FILE  *f;
	array *ek;

	xasprintf(&wdir, "%s%s/var/lib/portage", portroot, CONFIG_EPREFIX);
	xasprintf(&wpath, "%s/%s", wdir, fname);
	xasprintf(&tmp, "%s.qmerge.%d", wpath, (int)getpid());
	ek = set_keys(keepset);
	array_sort(ek, qm_strcmp_cb);
	f = fopen(tmp, "w");
	if (f != NULL) {
		size_t m;
		char  *e;
		bool   ok = true;

		array_for_each(ek, m, e)
			if (fprintf(f, "%s\n", e) < 0)
				ok = false;
		if (fclose(f) != 0)
			ok = false;
		if (!ok) {
			warnp("could not write %s", wpath);
			unlink(tmp);
		} else if (rename(tmp, wpath) != 0) {
			warnp("could not update %s", wpath);
			unlink(tmp);
		}
	} else {
		warnp("could not write %s", tmp);
	}
	array_free(ek);
	free(tmp);
	free(wpath);
	free(wdir);
}

/* category optional on the arg,version ignored 
 * (world entries are versionless), and the two guards. a slotted arg should never removes a slotless entry, a
 * repo-qualified arg never removes a repo-less one */
static bool
qm_deselect_match(const char *arg, const char *wline)
{
	depend_atom *a;
	depend_atom *w;
	bool         m = false;

	a = atom_explode(arg);
	w = atom_explode(wline);
	if (a != NULL && w != NULL &&
			a->PN != NULL && w->PN != NULL &&
			strcmp(a->PN, w->PN) == 0 &&
			(a->CATEGORY == NULL || (w->CATEGORY != NULL &&
				strcmp(a->CATEGORY, w->CATEGORY) == 0)) &&
			!(a->SLOT != NULL && w->SLOT == NULL) &&
			(a->SLOT == NULL || w->SLOT == NULL ||
				strcmp(a->SLOT, w->SLOT) == 0) &&
			!(a->REPO != NULL && w->REPO == NULL) &&
			(a->REPO == NULL || w->REPO == NULL ||
				strcmp(a->REPO, w->REPO) == 0))
		m = true;
	if (a != NULL)
		atom_implode(a);
	if (w != NULL)
		atom_implode(w);
	return m;
}

/* read a world-family file into a set of trimmed lines */
static set *
qm_world_load(const char *fname)
{
	char   *wpath;
	char   *buf = NULL;
	size_t  len = 0;
	set    *entries = create_set();

	xasprintf(&wpath, "%s%s/var/lib/portage/%s",
			  portroot, CONFIG_EPREFIX, fname);
	if (eat_file(wpath, &buf, &len) && buf != NULL) {
		char *line;
		char *sp;

		for (line = strtok_r(buf, "\r\n", &sp);
			 line != NULL;
			 line = strtok_r(NULL, "\r\n", &sp))
		{
			char *t = rmspace(line);

			if (*t != '\0' && *t != '#')
				add_set_unique(t, entries, NULL);
		}
	}
	free(buf);
	free(wpath);
	return entries;
}

/* the standalone --deselect action: prune the captured atoms/@sets from
 * world and world_sets, merge nada. */
static int
qm_deselect_run(void)
{
	set    *world;
	set    *wsets;
	array  *lines;
	array  *args;
	size_t  n;
	size_t  m;
	char   *w;
	char   *k;
	int     removed = 0;
	bool    ok;
	const char *verb = pretend ? "Would remove" : "Removing";

	world = qm_world_load("world");
	lines = set_keys(world);
	array_sort(lines, qm_strcmp_cb);
	if (qm_world_select != NULL) {
		args = set_keys(qm_world_select);
		array_for_each(lines, n, w) {
			array_for_each(args, m, k) {
				if (!qm_deselect_match(k, w))
					continue;
				printf("%s>>>%s %s %s from \"world\" favorites file...\n",
					   GREEN, NORM, verb, w);
				removed++;
				if (!pretend)
					del_set(w, world, &ok);
				break;
			}
		}
		array_free(args);
	}
	array_free(lines);
	if (removed > 0 && !pretend)
		qm_world_rewrite("world", world);
	free_set(world);

	wsets = qm_world_load("world_sets");
	if (qm_worldset_select != NULL) {
		int sremoved = 0;

		args = set_keys(qm_worldset_select);
		array_for_each(args, m, k) {
			if (contains_set(k, wsets) == NULL)
				continue;
			printf("%s>>>%s %s %s from \"world_sets\" file...\n",
				   GREEN, NORM, verb, k);
			removed++;
			sremoved++;
			if (!pretend)
				del_set(k, wsets, &ok);
		}
		array_free(args);
		if (sremoved > 0 && !pretend)
			qm_world_rewrite("world_sets", wsets);
	}
	free_set(wsets);

	if (removed == 0)
		printf(">>> No matching atoms found in \"world\" favorites "
			   "file...\n");
	return EXIT_SUCCESS;
}

/* implied deselect on -U/-e (identical to poratge). Drop world
 * entries whose cp was unmerged and no longer matches anything in the
 * VDB and entries still satisfied by another version/slot stay.
 * CLI @sets captured for the unmerge are dropped from world_sets like portage */
static void
qm_world_clean_unmerged(void)
{
	set      *world;
	array    *lines;
	size_t    n;
	char     *w;
	int       removed = 0;
	bool      ok;
	tree_ctx *vdb;

	if ((qm_unmerged_cps == NULL || cnt_set(qm_unmerged_cps) == 0) &&
			(qm_worldset_select == NULL ||
			 cnt_set(qm_worldset_select) == 0))
		return;

	vdb = tree_new(portroot, portvdb, TREETYPE_VDB, true);
	world = qm_world_load("world");
	lines = set_keys(world);
	array_sort(lines, qm_strcmp_cb);
	array_for_each(lines, n, w) {
		depend_atom *wa = atom_explode(w);
		char         cp[_Q_PATH_MAX];
		bool         gone;

		if (wa == NULL)
			continue;
		if (wa->CATEGORY == NULL || wa->PN == NULL) {
			atom_implode(wa);
			continue;
		}
		snprintf(cp, sizeof(cp), "%s/%s", wa->CATEGORY, wa->PN);
		if (qm_unmerged_cps == NULL ||
				contains_set(cp, qm_unmerged_cps) == NULL) {
			atom_implode(wa);
			continue;
		}
		gone = true;
		if (vdb != NULL) {
			array *t = tree_match_atom(vdb, wa,
					TREE_MATCH_LATEST  | TREE_MATCH_FIRST |
					TREE_MATCH_VIRTUAL | TREE_MATCH_ACCT);

			gone = array_cnt(t) == 0;
			array_free(t);
		}
		atom_implode(wa);
		if (!gone)
			continue;
		printf("%s>>>%s Removing %s from \"world\" favorites file...\n",
			   GREEN, NORM, w);
		del_set(w, world, &ok);
		removed++;
	}
	array_free(lines);
	if (vdb != NULL)
		tree_close(vdb);
	if (removed > 0)
		qm_world_rewrite("world", world);
	free_set(world);

	/* uninstall only and for the future: a merge-run soft-blocker unmerge reaches here
	 * too, and there qm_worldset_select holds sets being RECORDED */
	if (uninstall &&
			qm_worldset_select != NULL && cnt_set(qm_worldset_select) > 0) {
		set   *wsets = qm_world_load("world_sets");
		array *args  = set_keys(qm_worldset_select);
		size_t m;
		char  *k;
		int    sremoved = 0;

		array_for_each(args, m, k) {
			if (contains_set(k, wsets) == NULL)
				continue;
			printf("%s>>>%s Removing %s from \"world_sets\" file...\n",
				   GREEN, NORM, k);
			del_set(k, wsets, &ok);
			sremoved++;
		}
		array_free(args);
		if (sremoved > 0)
			qm_world_rewrite("world_sets", wsets);
		free_set(wsets);
	}
}

/* one labelled line of the --info report, skipped when empty */
static void
qm_info_meta(tree_pkg_ctx *p, const char *label, enum tree_pkg_meta_keys key)
{
	char *v = tree_pkg_meta(p, key);

	if (v != NULL && *v != '\0')
		printf("  %s%-14s%s %s\n", DKBLUE, label, NORM, v);
}

static void
qm_info_vdb(const atom_ctx *pa, const char *file, const char *label)
{
	char    path[_Q_PATH_MAX];
	char   *buf = NULL;
	size_t  len = 0;

	snprintf(path, sizeof(path), "%s%s/%s/%s/%s",
			 portroot, portvdb, pa->CATEGORY, pa->PF, file);
	if (eat_file(path, &buf, &len) && buf != NULL) {
		(void)rmspace(buf);
		if (*buf != '\0')
			printf("  %s%-14s%s %s\n", DKBLUE, label, NORM, buf);
	}
	free(buf);
}

/* --info: precise how-was-this-compiled report. A pkg@repo selector 
 * reports the binhost catalog entry instead.
 * A plain atom with no installed match falls through to the
 * best binhost candidate with a notice. */
static int
qm_info_run(set *todo)
{
	array  *keys = set_keys(todo);
	size_t  i;
	char   *k;
	int     rc = EXIT_SUCCESS;

	array_for_each(keys, i, k) {
		atom_ctx     *a;
		atom_ctx     *pa;
		tree_pkg_ctx *p       = NULL;
		bool          frombin = false;

		a = atom_explode(k);
		if (a == NULL)
			continue;
		if (a->REPO != NULL && a->REPO[0] == '@') {
			p       = best_version(a, BV_BINPKG);
			frombin = true;
		} else {
			p = best_version(a, BV_INSTALLED);
			if (p == NULL) {
				p       = best_version(a, BV_BINPKG);
				frombin = p != NULL;
			}
		}
		if (p == NULL) {
			warn("no installed package or binhost candidate matches %s", k);
			rc = EXIT_FAILURE;
			atom_implode(a);
			continue;
		}
		pa = tree_pkg_atom(p, true);

		printf("%s%s/%s%s %s\n", BOLD, pa->CATEGORY, pa->PF, NORM,
			   frombin ? "(binhost candidate)" : "(installed)");
		qm_info_meta(p, "SLOT:", Q_SLOT);
		qm_info_meta(p, "repository:", Q_repository);
		qm_info_meta(p, "BUILD_ID:", Q_BUILD_ID);
		{
			char   *bt = tree_pkg_meta(p, Q_BUILD_TIME);
			time_t  t  = bt != NULL ? (time_t)strtoull(bt, NULL, 10) : 0;

			if (t > 0) {
				char tb[64];

				strftime(tb, sizeof(tb), "%Y-%m-%d %H:%M:%S %Z",
						 localtime(&t));
				printf("  %s%-14s%s %s (%s)\n", DKBLUE, "BUILD_TIME:",
					   NORM, bt, tb);
			}
		}
		qm_info_meta(p, "EAPI:", Q_EAPI);
		qm_info_meta(p, "KEYWORDS:", Q_KEYWORDS);
		qm_info_meta(p, "CHOST:", Q_CHOST);
		if (!frombin) {
			qm_info_vdb(pa, "CBUILD",       "CBUILD:");
			qm_info_vdb(pa, "CFLAGS",       "CFLAGS:");
			qm_info_vdb(pa, "CXXFLAGS",     "CXXFLAGS:");
			qm_info_vdb(pa, "LDFLAGS",      "LDFLAGS:");
			qm_info_vdb(pa, "FEATURES",     "FEATURES:");
			qm_info_vdb(pa, "INSTALL_MASK", "INSTALL_MASK:");
			qm_info_vdb(pa, "COUNTER",      "COUNTER:");
		}
		qm_info_meta(p, "IUSE:", Q_IUSE);
		qm_info_meta(p, "USE:", Q_USE);
		qm_info_meta(p, "DEPEND:", Q_DEPEND);
		qm_info_meta(p, "RDEPEND:", Q_RDEPEND);
		qm_info_meta(p, "PDEPEND:", Q_PDEPEND);
		qm_info_meta(p, "BDEPEND:", Q_BDEPEND);
		qm_info_meta(p, "IDEPEND:", Q_IDEPEND);
		qm_info_meta(p, "REQUIRES:", Q_REQUIRES);
		qm_info_meta(p, "PROVIDES:", Q_PROVIDES);
		if (frombin) {
			qm_info_meta(p, "PATH:", Q_PATH);
			qm_info_meta(p, "SIZE:", Q_SIZE);
			qm_info_meta(p, "MD5:", Q_MD5);
		}
		if (verbose) {
			static const struct {
				const char             *lbl;
				enum tree_pkg_meta_keys k;
			} dc[] = {
				{ "resolved DEPEND:",  Q_DEPEND  },
				{ "resolved RDEPEND:", Q_RDEPEND },
				{ "resolved PDEPEND:", Q_PDEPEND },
				{ "resolved BDEPEND:", Q_BDEPEND },
				{ "resolved IDEPEND:", Q_IDEPEND },
			};
			tree_ctx *vdb = tree_new(portroot, portvdb,
									 TREETYPE_VDB, true);
			set      *use = set_add_from_string(NULL,
									tree_pkg_meta(p, Q_USE));
			size_t    di;

			for (di = 0; vdb != NULL &&
					di < sizeof(dc) / sizeof(dc[0]); di++) {
				char       *ds = tree_pkg_meta(p, dc[di].k);
				dep_node_t *dt;
				array      *fl;
				size_t      fi;
				void       *fa;

				if (ds == NULL || *ds == '\0')
					continue;
				dt = dep_grow_tree(ds);
				if (dt == NULL)
					continue;
				dep_resolve_tree(dt, vdb, use, NULL, NULL);

				fl = dep_nodes(dt);
				printf("  %s%-18s%s", DKBLUE, dc[di].lbl, NORM);
				array_for_each(fl, fi, fa) {
					dep_node_t   *nd = (dep_node_t *)fa;
					tree_pkg_ctx *rp = dep_node_pkg(nd);
					atom_ctx     *na = dep_node_atom(nd);

					if (na != NULL && na->blocker != ATOM_BL_NONE)
						printf(" %s(blocks)%s %s", YELLOW, NORM,
							   atom_to_string(na));
					else if (rp != NULL)
						printf(" %s", atom_format("%[CAT]%[PF]",
								tree_pkg_atom(rp, true)));
					else
						printf(" %s(unresolved)%s %s", RED, NORM,
							   atom_format("%[CAT]%[PF]", na));
				}
				printf("\n");
				array_free(fl);
				dep_burn_tree(dt);
			}
			if (use != NULL)
				free_set(use);
			if (vdb != NULL)
				tree_close(vdb);
		}
		if (verbose && !frombin) {
			char    npath[_Q_PATH_MAX];
			char   *nbuf = NULL;
			size_t  nlen = 0;

			snprintf(npath, sizeof(npath), "%s%s/%s/%s/NEEDED.ELF.2",
					 portroot, portvdb, pa->CATEGORY, pa->PF);
			if (eat_file(npath, &nbuf, &nlen) && nbuf != NULL &&
					*nbuf != '\0') {
				char *nl;
				char *nsave;

				printf("  %s%-14s%s\n", DKBLUE, "NEEDED.ELF.2:", NORM);
				for (nl = strtok_r(nbuf, "\n", &nsave);
					 nl != NULL;
					 nl = strtok_r(NULL, "\n", &nsave))
					printf("    %s\n", nl);
			}
			free(nbuf);
		}
		printf("\n");
		atom_implode(a);
	}
	array_free(keys);
	return rc;
}

#if defined(__GLIBC__) && defined(Q_STATIC_BUILD)
/* glibc's getaddrinfo dlopens the nsswitch.conf hosts modules even
 * from a static binary, and a shared NSS module executing inside a
 * static process segfaults (libnss_systemd and friends).
 * Pin this process to the builtin files+dns backends (in-libc since glibc
 * 2.32) so a static q resolves safely under *ANY* nsswitch.conf.
 * Dynamic builds keep full NSS behaviour. If glibc ever drops this
 * internal symbol, the fallback will be res_query + CURLOPT_RESOLVE. 
 * We're mostly hoping and testing here, don't take this for granted. */
extern int __nss_configure_lookup(const char *dbname, const char *config);
#endif

int qmerge_main(int argc, char **argv)
{
	int i, ret;
	int deselect_action = 0;
	set *todo;
	bool regen_index = false;
	int list_repos = 0;
	int list_sets = 0;
	int show_info = 0;

#if defined(__GLIBC__) && defined(Q_STATIC_BUILD)
	__nss_configure_lookup("hosts", "files dns");
#endif

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
			case 'f': fetch_only = 1;
					  force_download = 1;
					  interactive = 0;     break;
			case 'F': force_download = 2;  break;
			case 's': search_pkgs = 1;
					  interactive = 0;     break;
			case 131: show_phases = 1;
					  interactive = 0;     break;
			case 143: no_phases = 1;       break;
			case 132: qm_backtrack = atoi(optarg); break;
			/* case 'i': case 'g': */
			case 'K': install = 1;         break;
			case 'U': uninstall = 1;       break;
			case 'e': uninstall = 1;
					  uninstall_force = 1; break;
			case 'p': pretend = 1;         break;
			case 'N': newuse = 1;          break;
			case 'n': noreplace = 1;       break;
			case 'W': qm_deselect = (optarg != NULL &&
									 (*optarg == 'n' || *optarg == 'N' ||
									  *optarg == '0' || *optarg == 'f'))
									 ? 0 : 1;
					  break;
			case 133: rebuilt_bins = (optarg == NULL ||
									  *optarg == 'y' || *optarg == '1' ||
									  *optarg == 't' || *optarg == 'T')
									  ? 1 : 0;
					  break;
			case 137: qm_rebuilt_ts = strtoull(optarg, NULL, 10);
					  qm_rebuilt_ts_set = 1;
					  break;
			case 'u': update_only = 1;
					  install = 1;         break;
			case 'D': deep = 1;
					  install = 1;         break;
			case 'y': interactive = 0;     break;
			case '1': oneshot = 1;         break;
			case 'O': follow_rdepends = 0; break;
			case 'i': regen_index = true;   break;
			case 130: fetch_only = 1;
					  force_download = 1;
					  interactive = 0;      break;
			case 'j': qmerge_jobs = qm_parse_jobs(optarg); break;
			case 134: qm_parse_usepkg_exclude(optarg, "--usepkg-exclude");
					  break;
			case 140: qm_parse_exclude(optarg, "--exclude");  break;
			case 135: qm_excl_live = 1;    break;
			case 136: qm_respect_use = (*optarg == 'y' || *optarg == '1' ||
										*optarg == 't' || *optarg == 'T')
										? 1 : 0;
					  break;
			case 141: qm_parse_gb_atoms(&qm_gb_excl_cli, optarg,
										"--getbinpkg-exclude");
					  break;
			case 142: qm_parse_gb_atoms(&qm_gb_incl_cli, optarg,
										"--getbinpkg-include");
					  break;
			case 138: list_repos = 1;      break;
			case 144: list_sets = 1;       break;
			case 145: show_info = 1;
					  interactive = 0;     break;
			case 146: qm_search_exact = true; break;
			case 147: qm_keep_going = (optarg == NULL ||
									   *optarg == 'y' || *optarg == '1' ||
									   *optarg == 't' || *optarg == 'T')
									   ? 1 : 0;
					  break;
			case 127: keep_work = true;    break;
			case 128: debug = true;        break;
			COMMON_GETOPTS_CASES(qmerge)
		}
	}

	if (list_repos)
		return qm_print_repos();

	if (list_sets) {
		set   *ls = NULL;
		array *keys;
		size_t n;
		char  *a;

		if (optind >= argc) {
			warn("--list-set needs set names to expand (e.g. @world)");
			return EXIT_FAILURE;
		}
		for (i = optind; i < argc; i++)
			ls = qmerge_add_set(argv[i], ls);
		if (ls == NULL)
			return EXIT_SUCCESS;
		keys = set_keys(ls);
		array_sort(keys, qm_strcmp_cb);
		array_for_each(keys, n, a)
			if (n == 0 || strcmp(a, (char *)array_get(keys, n - 1)) != 0)
				printf("%s\n", a);
		array_free(keys);
		free_set(ls);
		return EXIT_SUCCESS;
	}

	if (regen_index)
		return binpkg_index_regen();

	/* -q (quiet) only reduces output; it must NOT imply the merge prompt is
	 * skipped, use -y for non-interactive/auto-confirm.
	 * For fully unattended runs combine them: `qmerge -f -q -y <pkg>`. */

	/* backtrack precedence: --backtrack has prio over $QMERGE_BACKTRACK has prio over
	 * the built-in default (portage's is 20) */
	if (qm_backtrack < 0) {
		const char *eb = getenv("QMERGE_BACKTRACK");

		qm_backtrack = eb != NULL && *eb != '\0' ? atoi(eb) : 20;
	}

	if (!no_phases) {
		const char *np = qm_config_var("QMERGE_NO_PHASES");

		if (np != NULL && (*np == '1' || *np == 'y' || *np == 'Y'))
			no_phases = 1;
	}
	if (no_phases)
		warn("--no-phases: pkg_* phases will be SKIPPED, not run; each "
			 "skip is recorded in %svar/lib/portage/.qmerge-skipped-phases",
			 portroot);

	/* quiet` itself is force-toggled by the interactive preview run */
	qm_user_quiet   = quiet;
	qm_user_verbose = verbose;

	/* QMERGE_LENIENT_UPGRADE (default 1): when a strand has no acceptable
	 * rebuilt binpkg, lenient proceeds with the provider upgrade and warns
	 * about the dangling pin (portage behavior); strict holds the provider
	 * back and drops planned rebuilds that pin the new version */
	/* lenient-upgrade precedence: $QMERGE_LENIENT_UPGRADE (env prio over
	 * make.conf) prio over the built-in default (lenient, like portage) */
	if (qm_lenient < 0) {
		const char *lv = qmerge_lenient_conf;

		if (lv != NULL && *lv != '\0')
			qm_lenient = (*lv == '0' || *lv == 'n' || *lv == 'N' ||
						  *lv == 'f' || *lv == 'F') ? 0 : 1;
		else
			qm_lenient = 1;
	}

	/* QMERGE_KEEP_GOING feature (default 0 = classic abort on 1st fail. CLI
	 * --keep-going has priority, then env-over-make.conf like the knobs above) */
	if (qm_keep_going < 0) {
		const char *kv = qmerge_keep_going_conf;

		if (kv != NULL && *kv != '\0')
			qm_keep_going = (*kv == 'y' || *kv == 'Y' || *kv == '1' ||
							 *kv == 't' || *kv == 'T') ? 1 : 0;
		else
			qm_keep_going = 0;
	}

	/* QMERGE_SLOT_UNIFY (default 1, env prio over make.conf) */
	if (qm_slot_unify < 0) {
		const char *sv = getenv("QMERGE_SLOT_UNIFY");

		if (sv == NULL || *sv == '\0')
			sv = qm_config_var("QMERGE_SLOT_UNIFY");
		if (sv != NULL && *sv != '\0')
			qm_slot_unify = (*sv == '0' || *sv == 'n' || *sv == 'N' ||
							 *sv == 'f' || *sv == 'F') ? 0 : 1;
		else
			qm_slot_unify = 1;
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
	/* --exclude has priority over $QMERGE_EXCLUDE (env), same as usepkg-exclude */
	if (qm_exclude == NULL) {
		const char *ee = getenv("QMERGE_EXCLUDE");

		if (ee != NULL && *ee != '\0')
			qm_parse_exclude(ee, "QMERGE_EXCLUDE");
	}
	if (!qm_excl_live) {
		const char *el = getenv("QMERGE_USEPKG_EXCLUDE_LIVE");

		if (el != NULL && *el != '\0' && strcmp(el, "0") != 0)
			qm_excl_live = 1;
	}
	/* --getbinpkg-exclude/-include has priority over QMERGE_GETBINPKG_* envs */
	if (qm_gb_excl_cli == NULL) {
		const char *ee = getenv("QMERGE_GETBINPKG_EXCLUDE");

		if (ee != NULL && *ee != '\0')
			qm_parse_gb_atoms(&qm_gb_excl_cli, ee,
							  "QMERGE_GETBINPKG_EXCLUDE");
	}
	if (qm_gb_incl_cli == NULL) {
		const char *ee = getenv("QMERGE_GETBINPKG_INCLUDE");

		if (ee != NULL && *ee != '\0')
			qm_parse_gb_atoms(&qm_gb_incl_cli, ee,
							  "QMERGE_GETBINPKG_INCLUDE");
	}

	if (rebuilt_bins < 0) {
		const char *rb = qmerge_rebuilt_conf;

		/* Preparing to implement a very interesting feature we
		 * deduced from observations.
		 * basically and in short: we need to somehow keep
		 * the local newly built (via portage) pkgs, and not
		 * take the remote earlier built packages.
		 * So we'll have a 'newer' string setup for a new QMERGE
		 * feature called QMERGE_REBUILT_BINARIES="*".
		 * We're not exactly sure what the default should be, though.  */
		if (rb != NULL && strcasecmp(rb, "newer") == 0) {
			rebuilt_bins = 1;
			if (!qm_rebuilt_ts_set) {
				qm_rebuilt_ts     = 0;
				qm_rebuilt_ts_set = 1;
			}
		} else if (rb != NULL && *rb != '\0')
			rebuilt_bins = (*rb == 'y' || *rb == '1' ||
							*rb == 't' || *rb == 'T') ? 1 : 0;
		else
			rebuilt_bins = deep ? 1 : 0;
	}

	/* --binpkg-respect-use beats $QMERGE_BINPKG_RESPECT_USE (env prio over
	 * make.conf, per the config framework) */
	if (qm_respect_use < 0) {
		const char *ru = qmerge_respect_use_conf;

		if (ru != NULL && *ru != '\0')
			qm_respect_use = (*ru == 'y' || *ru == '1' ||
							  *ru == 't' || *ru == 'T') ? 1 : 0;
	}

	/* copy pasta from portage. the --deselect with no explicit action is its own
	 * action, prune world entries and merge nuffin. */
	deselect_action = (qm_deselect == 1 && !install && !uninstall);

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
		for (i = optind; i < argc; ++i) {
			if ((!uninstall && !oneshot) || deselect_action)
				qm_world_capture(argv[i]);
			else if (uninstall && argv[i][0] == '@')
				/* for the implied world_sets deselect */
				qm_world_capture(argv[i]);
			todo = qmerge_add_set(argv[i], todo);
		}

	if (search_pkgs == 0 && show_phases == 0 && todo == NULL &&
			force_download != 1) {
		warn("need package names to work with");
		return EXIT_FAILURE;
	}

	if (deselect_action) {
		ret = qm_deselect_run();
		goto cleanup;
	}

	if (show_info) {
		ret = qm_info_run(todo);
		goto cleanup;
	}

	/* --noreplace: drop named targets an installed package already
	 * satisfies*/
	if (noreplace && !uninstall && todo != NULL) {
		array *keys = set_keys(todo);
		size_t n;
		char  *k;
		bool   ok;

		array_for_each(keys, n, k) {
			atom_ctx *a = atom_explode(k);

			if (a == NULL)
				continue;
			if (best_version(a, BV_INSTALLED) != NULL) {
				atom_implode(a);
				del_set(k, todo, &ok);
				continue;
			}
			atom_implode(a);
		}
		array_free(keys);
		if (cnt_set(todo) == 0) {
			free_set(todo);
			todo = NULL;
			if (!pretend && interactive &&
					!qmerge_prompt("OK add these packages to world file")) {
				ret = EXIT_FAILURE;
				goto cleanup;
			}
		}
	}

	/* -s with no local Packages index: bootstrap by fetching it, so a
	 * fresh binhost eater can search right away; -fs forces a
	 * refresh even when a cached index exists.
	 * Check every repo's OWN store (location= aware), checking 
	 * PKGDIR alone forced a refetch on every search when the 
	 * sole repo stores elsewhere. */
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

			if ((size_t)snprintf(idx, sizeof(idx), "%s%.*s/%s",
								 portroot, (int)(sizeof(idx) - 16),
								 loc, Packages) >= sizeof(idx))
				continue;
			if (stat(idx, &st) == 0 && st.st_size > 0) {
				found = true;
				break;
			}
		}
		if (!found)
			force_download = 1;
	}

	/* bare -f, the very documented refresh-the-index form */
	if (force_download == 1 && !uninstall && !search_pkgs &&
			argc - optind == 0)
		qm_index_force = true;

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
		size_t ri;
		size_t usable = 0;

		binrepos_load();
		for (ri = 0; ri < qm_nbinrepos; ri++)
			if (qm_binrepos[ri].uri != NULL &&
					qm_binrepos[ri].uri[0] != '\0')
				usable++;
		if (usable == 0)
			warn("no binhosts configured; nothing to fetch. Add a "
				 "[repo] section with sync-uri to /etc/portage/"
				 "binrepos.conf or set PORTAGE_BINHOST in make.conf");
		else if (argc - optind > 0)
			warn("the given arguments expanded to no packages; "
				 "nothing to fetch");
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
	if (interactive && todo != NULL) {
		char save_pretend = pretend;
		int  save_verbose = verbose;
		int  save_quiet   = quiet;

		/* start the dry run with a clean queued-packages state */
		if (qmerge_processed_pkgs != NULL) {
			free_set(qmerge_processed_pkgs);
			qmerge_processed_pkgs = NULL;
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
		if (qmerge_processed_pkgs != NULL) {
			free_set(qmerge_processed_pkgs);
			qmerge_processed_pkgs = NULL;
		}

		pretend = save_pretend;
		verbose = save_verbose;
		quiet = save_quiet;
	}

	qm_run_trust_helper();

	ret = qmerge_run(todo);

	if (install && !uninstall && !pretend && !fetch_only && !oneshot &&
			ret == EXIT_SUCCESS) {
		qm_world_update();
		qm_worldsets_update();
	}

 cleanup:
	if (todo != NULL)
		free_set(todo);

	if (qmerge_processed_pkgs != NULL) {
		free_set(qmerge_processed_pkgs);
		qmerge_processed_pkgs = NULL;
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

	qm_use_rejects_flush();
	qm_demands_free();
	qm_blk_reset();
	if (qm_exec_failed != NULL) {
		free_set(qm_exec_failed);
		qm_exec_failed = NULL;
	}
	if (qm_kg_mask != NULL) {
		free_set(qm_kg_mask);
		qm_kg_mask = NULL;
	}
	if (qm_kg_done != NULL) {
		array  *dv = hash_values(qm_kg_done);
		size_t  dn;
		char   *dslot;

		array_for_each(dv, dn, dslot)
			free(dslot);
		array_free(dv);
		hash_free(qm_kg_done);
		qm_kg_done = NULL;
	}
	if (qm_kg_failed != NULL) {
		array_deepfree(qm_kg_failed, free);
		qm_kg_failed = NULL;
	}
	if (qm_unify_mask != NULL) {
		free_set(qm_unify_mask);
		qm_unify_mask = NULL;
	}
	if (qm_unsat_noted != NULL) {
		free_set(qm_unsat_noted);
		qm_unsat_noted = NULL;
	}
	if (qm_use_accepts != NULL) {
		array *av = hash_values(qm_use_accepts);

		array_deepfree(av, free);
		hash_free(qm_use_accepts);
		qm_use_accepts = NULL;
	}
	qm_preserved_finish();
	if (qm_force_targets != NULL) {
		free_set(qm_force_targets);
		qm_force_targets = NULL;
	}
	if (qm_exclude_noted != NULL) {
		free_set(qm_exclude_noted);
		qm_exclude_noted = NULL;
	}
	if (qm_exclude != NULL) {
		size_t       n;
		depend_atom *x;

		array_for_each(qm_exclude, n, x)
			atom_implode(x);
		array_free(qm_exclude);
		qm_exclude = NULL;
	}
	if (qm_lic_rejects != NULL) {
		free_set(qm_lic_rejects);
		qm_lic_rejects = NULL;
	}
	if (qm_soft_unmerge != NULL) {
		free_set(qm_soft_unmerge);
		qm_soft_unmerge = NULL;
	}
	if (qm_world_select != NULL) {
		free_set(qm_world_select);
		qm_world_select = NULL;
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

		array_deepfree(nv, set_free_cb);
		hash_free(qm_plan_notices);
		qm_plan_notices = NULL;
	}
	if (qmerge_vdb_tree != NULL)
		tree_close(qmerge_vdb_tree);

	return ret;
}
