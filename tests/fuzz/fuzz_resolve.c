/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * fuzz the resolver of qmerge: a pretend run and the search, in-process.
 * the big boy.
 * 
 * the input is the body of a Packages index. it is written into a small
 * fixed ROOT (six installed packages, a world file, an own profile and
 * config), then qmerge_main is called with -p or -s.
 *
 * qmerge keeps its args flags in global variables, so they are
 * put back to their defaults before every run (fuzz_reset_options).
 * new flag in qmerge.c needs a line there.
 *
 * qmerge.c and main.c are compiled into this translation unit with main
 * renamed, model from fuzz_dcx.c. build-dcx.sh links the rest of q around
 * it. fuzz testing lane only.
 *
 * input: the first byte picks the args passed by env call, the rest is the index.
 */
#define main q_real_main
#include "../../main.c"
#undef main
#include "../../qmerge.c"

static char fuzz_base[4096];
static char fuzz_index[8192];

static void fuzz_wfile
(
  const char *dir,
  const char *name,
  const char *content
)
{
  char  p[8192];
  FILE *f;

  mkdir_p(dir, 0755);
  snprintf(p, sizeof(p), "%s/%s", dir, name);
  f = fopen(p, "w");
  if (f == NULL)
    return;
  fputs(content, f);
  fclose(f);
}

static void fuzz_vdbpkg
(
  const char *cat,
  const char *pf,
  const char *slot,
  const char *use,
  const char *rdepend
)
{
  char d[8192];
  char v[8192];

  snprintf(d, sizeof(d), "%s/root/var/db/pkg/%s/%s", fuzz_base, cat, pf);
  snprintf(v, sizeof(v), "%s\n", slot);
  fuzz_wfile(d, "SLOT", v);
  snprintf(v, sizeof(v), "%s\n", rdepend);
  fuzz_wfile(d, "RDEPEND", v);
  snprintf(v, sizeof(v), "%s\n", use);
  fuzz_wfile(d, "USE", v);
  snprintf(v, sizeof(v), "%s\n", cat);
  fuzz_wfile(d, "CATEGORY", v);
  snprintf(v, sizeof(v), "%s\n", pf);
  fuzz_wfile(d, "PF", v);
  fuzz_wfile(d, "DEPEND", "\n");
  fuzz_wfile(d, "IDEPEND", "\n");
  fuzz_wfile(d, "PDEPEND", "\n");
  fuzz_wfile(d, "BDEPEND", "\n");
  fuzz_wfile(d, "KEYWORDS", "amd64\n");
  fuzz_wfile(d, "EAPI", "8\n");
  fuzz_wfile(d, "IUSE", "a b\n");
  fuzz_wfile(d, "COUNTER", "1\n");
  fuzz_wfile(d, "BUILD_TIME", "1\n");
  fuzz_wfile(d, "CONTENTS", "");
}

static void fuzz_config
(
  void
)
{
  char d[8192];
  char v[8192];

  snprintf(d, sizeof(d), "%s/root/var/lib/portage", fuzz_base);
  fuzz_wfile(d, "world", "dc-libs/F\ndc-libs/D\nvirtual/v\n");

  snprintf(d, sizeof(d), "%s/cfg/etc/portage", fuzz_base);
  fuzz_wfile(d, "make.conf",
             "FEATURES=\"\"\n"
             "ACCEPT_KEYWORDS=\"amd64\"\n"
             "ACCEPT_LICENSE=\"* -EULA @FREE\"\n"
             "USE=\"a\"\n");
  fuzz_wfile(d, "package.mask", "=dc-libs/A-2\n");
  fuzz_wfile(d, "package.use", "dc-libs/N b\n");
  fuzz_wfile(d, "package.license", "dc-libs/F EULA\n");
  fuzz_wfile(d, "package.accept_keywords", "dc-libs/F ~amd64\n");
  snprintf(v, sizeof(v),
           "[DEFAULT]\nmain-repo = gentoo\n[gentoo]\nlocation = %s/repo\n",
           fuzz_base);
  fuzz_wfile(d, "repos.conf", v);

  snprintf(d, sizeof(d), "%s/cfg/etc/portage/make.profile", fuzz_base);
  fuzz_wfile(d, "make.defaults",
             "ARCH=\"amd64\"\nUSE_EXPAND=\"L10N\"\nL10N=\"en\"\n");
  fuzz_wfile(d, "packages", "*dc-libs/B\n");
  fuzz_wfile(d, "use.mask", "m\n");
  fuzz_wfile(d, "use.force", "f\n");

  snprintf(d, sizeof(d), "%s/repo/profiles", fuzz_base);
  fuzz_wfile(d, "repo_name", "gentoo\n");
  fuzz_wfile(d, "license_groups", "FREE GPL-2 MIT\n");

  snprintf(d, sizeof(d), "%s/tmp", fuzz_base);
  mkdir_p(d, 0755);
  snprintf(d, sizeof(d), "%s/root/pkgs", fuzz_base);
  mkdir_p(d, 0755);
  snprintf(fuzz_index, sizeof(fuzz_index), "%s/Packages", d);

  fuzz_vdbpkg("dc-libs", "A-1", "0",   "a",   "");
  fuzz_vdbpkg("dc-libs", "B-1", "0",   "a",   "");
  fuzz_vdbpkg("dc-libs", "C-1", "0/1", "a b", "dc-libs/B");
  fuzz_vdbpkg("dc-libs", "D-1", "0",   "a",
              "a? ( dc-libs/A:= ) !a? ( dc-libs/B )");
  fuzz_vdbpkg("dc-libs", "F-1", "0",   "",    "dc-libs/C[a]");
  fuzz_vdbpkg("virtual", "v-1", "0",   "",    "|| ( dc-libs/A dc-libs/B )");
}

static void fuzz_reset_options
(
  void
)
{
  no_phases = 0;
  qm_backtrack = -1;
  install = 0;
  uninstall = 0;
  pretend = 0;
  newuse = 0;
  noreplace = 0;
  qm_deselect = -1;
  rebuilt_bins = -1;
  qm_rebuilt_ts = 0;
  update_only = 0;
  deep = 0;
  interactive = 1;
  oneshot = 0;
  follow_rdepends = 1;
  fetch_only = 0;
  qmerge_jobs = -1;
  qm_excl_live = 0;
  qm_respect_use = -1;
  qm_search_exact = false;
  qm_keep_going = -1;
  qm_depclean = 0;
  qm_dc_bdeps = -1;
  qm_dc_libcheck = -1;
  qm_verbose_conflicts = 0;
  keep_work = false;
  debug = false;
  search_pkgs = 0;
  force_download = 0;
  qm_slot_unify = -1;
  qm_user_verbose = 0;
  qm_user_quiet = 0;
  show_phases = 0;
  qm_index_force = false;
  qm_plan_empty = false;
  verbose = 0;
  quiet = 0;
}

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerInitialize
(
  int    *argc,
  char ***argv
)
{
  char d[8192];
  char cwd[4096];
  int  i;

  (void)argc;
  (void)argv;
  if (getcwd(cwd, sizeof(cwd)) == NULL)
    return 0;
  snprintf(fuzz_base, sizeof(fuzz_base), "%s/tests/r/tmp/fuzz_resolve", cwd);
  fuzz_config();

  snprintf(d, sizeof(d), "%s/root", fuzz_base);
  setenv("ROOT", d, 1);
  snprintf(d, sizeof(d), "%s/cfg", fuzz_base);
  setenv("PORTAGE_CONFIGROOT", d, 1);
  snprintf(d, sizeof(d), "%s/tmp", fuzz_base);
  setenv("PORTAGE_TMPDIR", d, 1);
  setenv("PKGDIR", "/pkgs", 1);
  setenv("QMERGE_NO_PHASES", "y", 1);

  warnout = stderr;
  argv0   = "fuzz_resolve";
  color_clear();
  overlays      = array_new();
  overlay_names = array_new();
  overlay_src   = array_new();
  for (i = 0; vars_to_read[i].name; ++i)
  {
    env_vars *var = &vars_to_read[i];

    switch (var->type)
    {
      case _Q_BOOL:
        *var->value.b = var->default_value;
        break;
      case _Q_STR:
      case _Q_NSTR:
      case _Q_ISTR:
        *var->value.s = xstrdup(var->default_value);
        break;
      case _Q_ISET:
        *var->value.t = (set *)q_deconst(var->default_value);
        break;
    }
    var->src = xstrdup(STR_DEFAULT);
  }
  set_portage_env_var(&vars_to_read[7], "true", "terminal");
  initialize_portage_env();
  if (getenv("FUZZ_SHOW") == NULL)
  {
    warnout = fopen("/dev/null", "w");
    if (freopen("/dev/null", "w", stdout) == NULL)
      return 0;
  }
  return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);
int LLVMFuzzerTestOneInput
(
  const uint8_t *data,
  size_t         size
)
{
  static const char *modes[][6] = {
    { "qmerge", "-p", "dc-libs/N", NULL },
    { "qmerge", "-pu", "@world", NULL },
    { "qmerge", "-puDN", "@world", NULL },
    { "qmerge", "-pv", "dc-libs/N", "dc-libs/M", NULL },
    { "qmerge", "-s", "dc", NULL },
    { "qmerge", "-pn", "dc-libs/N", "dc-libs/D", NULL },
    { "qmerge", "-puDNv", "@system", "dc-libs/N", NULL },
    { "qmerge", "-pO", "=dc-libs/M-2", NULL },
  };
  char *args[6];
  FILE *f;
  int   n;
  int   m;

  if (size == 0 || size > 4096)
    return 0;
  f = fopen(fuzz_index, "w");
  if (f == NULL)
    return 0;
  fputs("ARCH: amd64\nPACKAGES: 4\nTIMESTAMP: 1\nVERSION: 0\n\n", f);
  fwrite(data + 1, 1, size - 1, f);
  fclose(f);

  m = data[0] % (int)ARRAY_SIZE(modes);
  for (n = 0; modes[m][n] != NULL; n++)
    args[n] = xstrdup(modes[m][n]);
  args[n] = NULL;
  fuzz_reset_options();
  optind = 0;
  (void)qmerge_main(n, args);
  for (m = 0; m < n; m++)
    free(args[m]);
  return 0;
}
