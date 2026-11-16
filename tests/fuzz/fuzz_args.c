/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * fuzz the command line of qmerge, in-process, in pretend and search
 * mode only, against the same fixed ROOT, config and index as
 * fuzz_resolve.
 *
 * byte 1 picks the pretend or search prefix; the rest is cut at every
 * NUL byte into arguments: the first one is the option's value when
 * the option takes one, the others are the positional arguments. up
 * to 64 KiB, so arguments far above the parser targets' caps reach
 * the parsers through the command line.
 *
 * qmerge.c and main.c are compiled into this translation unit with main
 * renamed, copy paste from fuzz_dcx.c. build-dcx.sh links the rest of q
 * around it. fuzz testing lane only.
 */
#include "../../main.h"
#include <setjmp.h>
#if defined(__has_feature)
# if __has_feature(address_sanitizer)
#  define FUZZ_HAVE_LSAN 1
#  include <sanitizer/allocator_interface.h>
#  include <sanitizer/lsan_interface.h>
# endif
#endif

static jmp_buf fuzz_jmp;
static int     fuzz_in_run;

static void fuzz_exit(int status) __attribute__((noreturn));
#define exit(status) fuzz_exit(status)
#define main q_real_main
#include "../../main.c"
#undef main
#include "../../qmerge.c"
#undef exit

#ifdef FUZZ_HAVE_LSAN
#define FUZZ_PTRS (1u << 20)
static const volatile void *fuzz_ptrs[FUZZ_PTRS];
static size_t               fuzz_nptrs;
static int                  fuzz_blind;

static void fuzz_malloc_hook
(
  const volatile void *p,
  size_t               sz
)
{
  (void)sz;
  if (!fuzz_in_run)
    return;
  if (fuzz_nptrs < FUZZ_PTRS)
    fuzz_ptrs[fuzz_nptrs++] = p;
  else
    fuzz_blind = 1;
}

static void fuzz_free_hook
(
  const volatile void *p
)
{
  (void)p;
}

int __lsan_is_turned_off(void);
int __lsan_is_turned_off
(
  void
)
{
  return fuzz_blind;
}
#endif

static void fuzz_exit
(
  int status
)
{
  if (!fuzz_in_run)
    _exit(status);
#ifdef FUZZ_HAVE_LSAN
  {
    size_t i;

    for (i = 0; i < fuzz_nptrs; i++)
      __lsan_ignore_object((const void *)fuzz_ptrs[i]);
  }
#endif
  longjmp(fuzz_jmp, 1);
}

static char fuzz_base[4096];
static char fuzz_index[8192];

static const char fuzz_index_body[] =
  "ARCH: amd64\nPACKAGES: 4\nTIMESTAMP: 1\nVERSION: 0\n\n"
  "CPV: dc-libs/N-1\nSLOT: 0\nKEYWORDS: amd64\nDESC: a searchable description\n"
  "SIZE: 10\nPATH: dc-libs/N-1.gpkg.tar\n\n"
  "CPV: dc-libs/N-2\nSLOT: 0\nKEYWORDS: ~amd64\nSIZE: 2048\n"
  "PATH: dc-libs/N-2.gpkg.tar\n\n"
  "CPV: dc-libs/M-2\nSLOT: 0/2\nKEYWORDS: amd64\nRDEPEND: dc-libs/A:2\n"
  "SIZE: 10\nPATH: dc-libs/M-2.gpkg.tar\n\n"
  "CPV: virtual/dc-1\nSLOT: 0\nKEYWORDS: amd64\nRDEPEND: dc-libs/N\nSIZE: 1\n"
  "PATH: virtual/dc-1.gpkg.tar\n\n";

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
  snprintf(d, sizeof(d), "%s/cfg/etc/portage/sets", fuzz_base);
  fuzz_wfile(d, "own", "dc-libs/N\n@world\n");

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
  qm_dynamic_deps = -1;
  qm_no_env_update = false;
  qm_no_ldconfig = false;
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
  snprintf(fuzz_base, sizeof(fuzz_base), "%s/tests/r/tmp/fuzz_args", cwd);
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
  argv0   = "fuzz_args";
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
#ifdef FUZZ_HAVE_LSAN
  __sanitizer_install_malloc_and_free_hooks(fuzz_malloc_hook,
                                            fuzz_free_hook);
#endif
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
  static const char *const prefixes[][3] = {
    { "-p", NULL },
    { "-pv", NULL },
    { "-pU", NULL },
    { "-ps", NULL },
    { "-s", "--exact", NULL },
    { "-pc", NULL },
    { "-pD", NULL },
    { "-pO", NULL },
    { "-puDN", NULL },
    { "-py", NULL },
  };
  const struct option *opt;
  char                *tokens[8];
  char                *args[16];
  char                *body;
  char                *s;
  size_t               nopts;
  size_t               ntok = 0;
  size_t               i;
  FILE                *f;
  int                  n = 0;
  int                  m;
  bool                 positional = false;

  if (size < 2 ||
      size > 65536)
    return 0;
  for (nopts = 0; qmerge_long_opts[nopts].name != NULL; nopts++)
    ;
  opt = &qmerge_long_opts[data[0] % nopts];
  if (strcmp(opt->name, "root") == 0 ||
      strcmp(opt->name, "help") == 0 ||
      strcmp(opt->name, "version") == 0)
    return 0;

  f = fopen(fuzz_index, "w");
  if (f == NULL)
    return 0;
  fputs(fuzz_index_body, f);
  fclose(f);

  body = xmalloc(size - 2 + 1);
  memcpy(body, data + 2, size - 2);
  body[size - 2] = '\0';
  for (s = body; ntok < ARRAY_SIZE(tokens); s += strlen(s) + 1)
  {
    if (s >= body + (size - 2))
      break;
    tokens[ntok++] = s;
  }

  args[n++] = xstrdup("qmerge");
  m = data[1] % (int)ARRAY_SIZE(prefixes);
  for (i = 0; prefixes[m][i] != NULL; i++)
    args[n++] = xstrdup(prefixes[m][i]);
  i = 0;
  if (opt->has_arg != no_argument)
  {
    args[n++] = xasprintf("--%s=%s", opt->name, ntok > 0 ? tokens[0] : "");
    i = ntok > 0 ? 1 : 0;
  }
  else
  {
    args[n++] = xasprintf("--%s", opt->name);
  }
  args[n++] = xstrdup("--");
  for (; i < ntok && n < (int)ARRAY_SIZE(args) - 2; i++)
  {
    args[n++]  = xstrdup(tokens[i]);
    positional = true;
  }
  if (!positional)
    args[n++] = xstrdup("dc-libs/N");
  args[n] = NULL;

  fuzz_reset_options();
  optind = 0;
#ifdef FUZZ_HAVE_LSAN
  fuzz_nptrs = 0;
  fuzz_blind = 0;
#endif
  fuzz_in_run = 1;
  if (setjmp(fuzz_jmp) == 0)
    (void)qmerge_main(n, args);
  fuzz_in_run = 0;
  for (m = 0; m < n; m++)
    free(args[m]);
  free(body);
  return 0;
}
