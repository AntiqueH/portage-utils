/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * fuzz the small text helpers of qmerge that take strings from config
 * files, the command line and the binhost index.
 *
 * these helpers will be file-private functions of qmerge.c, so that file and
 * main.c are compiled into this translation unit with main renamed.
 *
 * input: the first byte picks the helper, the rest is its text.
 * if helpers take more than one string get the text split at newlines.
 */
#define main q_real_main
#include "../../main.c"
#undef main
#include "../../qmerge.c"

#define FUZZ_PARTS 4

static void fuzz_split
(
  char  *str,
  char **part
)
{
  size_t i;
  char  *nl;

  for (i = 0; i < FUZZ_PARTS; i++)
  {
    part[i] = str;
    nl = strchr(str, '\n');
    if (nl != NULL && i + 1 < FUZZ_PARTS)
    {
      *nl = '\0';
      str = nl + 1;
    }
    else
      str += strlen(str);
  }
}

static set *fuzz_words
(
  const char *str
)
{
  set  *ret;
  char *tmp;
  char *tok;
  char *sp;

  ret = create_set();
  tmp = xstrdup(str);
  for (tok = strtok_r(tmp, " \t", &sp);
       tok != NULL;
       tok = strtok_r(NULL, " \t", &sp))
    add_set_unique(tok, ret, NULL);
  free(tmp);
  return ret;
}

static void fuzz_shlex
(
  const char *str
)
{
  array  *toks;
  char   *tok;
  char   *quoted;
  size_t  i;

  toks = qm_shlex_split(str);
  array_for_each(toks, i, tok)
  {
    quoted = qm_shlex_quote(tok);
    free(quoted);
  }
  array_deepfree(toks, free);
}

static void fuzz_move
(
  char **part
)
{
  char *out;

  out = NULL;
  if (part[1][0] == '\0')
    return;
  if (qm_move_rewrite_str(part[0], part[1], part[2], &out))
    free(out);
}

static void fuzz_license
(
  char **part
)
{
  struct lic_acc   la;
  char           **toks;
  size_t           ntok;
  size_t           cap;
  size_t           i;
  char            *tmp;
  char            *tok;
  char            *sp;

  toks = NULL;
  ntok = 0;
  cap  = 0;
  la.acc        = create_set();
  la.den        = create_set();
  la.accept_all = false;
  la.use        = fuzz_words(part[1]);
  lic_add_tokens(part[0], &la);

  tmp = xstrdup(part[2]);
  for (tok = strtok_r(tmp, " \t\n", &sp);
       tok != NULL;
       tok = strtok_r(NULL, " \t\n", &sp))
  {
    if (ntok >= cap)
    {
      cap = cap > 0 ? cap * 2 : 16;
      toks = xrealloc(toks, sizeof(*toks) * cap);
    }
    toks[ntok++] = tok;
  }
  i = 0;
  (void)lic_parse_and(toks, ntok, &i, &la);

  free(toks);
  free(tmp);
  free_set(la.acc);
  free_set(la.den);
  free_set(la.use);
}

static void fuzz_buildid
(
  const char *str
)
{
  char out[_Q_PATH_MAX];

  (void)qm_arg_buildid(str, out, sizeof(out));
}

static void fuzz_varexpand
(
  char **part
)
{
  char *out;
  char *plain;

  out = qm_fetch_varexpand(part[0], part[1], part[2], part[3]);
  free(out);
  plain = unescape_fetchcommand(part[0]);
  free(plain);
}

static void fuzz_effective_use
(
  char **part
)
{
  set  *old_use;
  set  *old_force;
  set  *old_mask;
  char *out;

  old_use   = ev_use;
  old_force = use_force;
  old_mask  = use_mask;
  ev_use    = fuzz_words(part[2]);
  use_force = fuzz_words(part[3]);
  use_mask  = NULL;

  out = qm_effective_use(part[0], part[1]);
  free(out);

  free_set(ev_use);
  free_set(use_force);
  ev_use    = old_use;
  use_force = old_force;
  use_mask  = old_mask;
}

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerInitialize
(
  int    *argc,
  char ***argv
)
{
  void *prev;

  (void)argc;
  (void)argv;
  prev    = NULL;
  argv0   = "fuzz_qmhelpers";
  warnout = fopen("/dev/null", "w");
  if (warnout == NULL)
    warnout = stderr;

  license_groups = create_set();
  add_set_value("FREE", xstrdup("GPL-2 MIT @OSI"), &prev, license_groups);
  add_set_value("OSI", xstrdup("BSD @FREE -MIT"), &prev, license_groups);
  setenv("L10N", "en de", 1);
  setenv("ARCH", "amd64", 1);
  return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);
int LLVMFuzzerTestOneInput
(
  const uint8_t *data,
  size_t         size
)
{
  char *part[FUZZ_PARTS];
  char *str;

  if (size == 0 || size > 4096)
    return 0;
  str = xmalloc(size);
  memcpy(str, data + 1, size - 1);
  str[size - 1] = '\0';

  switch (data[0] % 7)
  {
    case 0:
      fuzz_shlex(str);
      break;
    case 1:
      fuzz_split(str, part);
      fuzz_move(part);
      break;
    case 2:
      fuzz_split(str, part);
      fuzz_license(part);
      break;
    case 3:
      (void)qm_arch_from_chost(str);
      break;
    case 4:
      fuzz_buildid(str);
      break;
    case 5:
      fuzz_split(str, part);
      fuzz_varexpand(part);
      break;
    case 6:
      fuzz_split(str, part);
      fuzz_effective_use(part);
      break;
  }

  free(str);
  return 0;
}
