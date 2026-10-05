/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 *
 * qetuto: a C reimplementation of app-portage/getuto (getuto 1.18),
 * maintaining ${ROOT}/etc/portage/gnupg so the Gentoo release keys are
 * trusted for binary-package signatures. Same behaviour that goes by
 * gpg/gpgconf.
 */

#include "main.h"
#include "applets.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdarg.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <xalloc.h>

#include "array.h"
#include "eat_file.h"
#include "rmspace.h"
#include "safe_io.h"
#include "set.h"
#include "stat-time.h"
#include "xvasprintf.h"
#include "xmkdir.h"

#define QETUTO_FLAGS "" COMMON_FLAGS
static struct option const qetuto_long_opts[] = {
  COMMON_LONG_OPTS
};
static const char * const qetuto_opts_help[] = {
  COMMON_OPTS_HELP
};
#define qetuto_usage(ret) usage(ret, QETUTO_FLAGS, qetuto_long_opts, \
    qetuto_opts_help, NULL, lookup_applet_idx("qetuto"))

static const char * const qet_keyservers_default[] = {
  "hkps://keys.openpgp.org",
  "hkps://keys.gentoo.org",
  NULL
};

#define QET_KEYS_DEFAULT "/usr/share/openpgp-keys/gentoo-release.asc"

#define QET_GPG_TERM "1.75m"
#define QET_GPG_KILL "2.5m"

static bool  qet_quiet = true;
static bool  qet_external;
static char  qet_home[_Q_PATH_MAX];
static char *qet_root;

/* NULL-terminated, built from QETUTO_KEYSERVERS / QETUTO_KEYS or the
 * Gentoo defaults; keyfiles are ROOT-prefixed absolute paths */
static char **qet_keyservers;
static char **qet_keyfiles;

/* split a whitespace/comma separated config value into a NULL-terminated
 * argv of xstrdup'd tokens.
 * TBD other details. */
static char **qet_split_list
(
  const char *s
)
{
  array *a   = array_new();
  char  *buf = xstrdup(s);
  char  *tok;
  char  *sp;
  char **out;
  size_t i;
  char  *e;

  for (tok = strtok_r(buf, " \t\r\n,", &sp);
       tok != NULL;
       tok = strtok_r(NULL, " \t\r\n,", &sp))
    if (tok[0] != '\0')
      array_append(a, xstrdup(tok));
  free(buf);

  out = xmalloc(sizeof(*out) * (array_cnt(a) + 1));
  array_for_each(a, i, e)
    out[i] = e;
  out[array_cnt(a)] = NULL;
  array_free(a);
  return out;
}

static void qet_build_lists(void)
{
  if (qetuto_keyservers_conf != NULL &&
      qetuto_keyservers_conf[0] != '\0')
  {
    qet_keyservers = qet_split_list(qetuto_keyservers_conf);
  }
  else
  {
    size_t k;
    size_t n = 0;

    while (qet_keyservers_default[n] != NULL)
      n++;
    qet_keyservers = xmalloc(sizeof(*qet_keyservers) * (n + 1));
    for (k = 0; k < n; k++)
      qet_keyservers[k] = xstrdup(qet_keyservers_default[k]);
    qet_keyservers[n] = NULL;
  }

  {
    const char *spec = (qetuto_keys_conf != NULL && qetuto_keys_conf[0] != '\0')
                           ? qetuto_keys_conf
                           : QET_KEYS_DEFAULT;
    char       *all =
        xasprintf("%s %s", spec,
                  qetuto_extra_keys_conf != NULL ? qetuto_extra_keys_conf : "");
    char **rel = qet_split_list(all);
    size_t n   = 0;
    size_t i;

    free(all);
    while (rel[n] != NULL)
      n++;
    qet_keyfiles = xmalloc(sizeof(*qet_keyfiles) * (n + 1));
    for (i = 0; i < n; i++)
    {
      char p[_Q_PATH_MAX];

      snprintf(p, sizeof(p), "%s%s%s", qet_root, rel[i][0] == '/' ? "" : "/",
               rel[i]);
      qet_keyfiles[i] = xstrdup(p);
      free(rel[i]);
    }
    qet_keyfiles[n] = NULL;
    free(rel);
  }
}

static void qet_free_lists(void)
{
  size_t i;

  if (qet_keyservers != NULL)
  {
    for (i = 0; qet_keyservers[i] != NULL; i++)
      free(qet_keyservers[i]);
    free(qet_keyservers);
    qet_keyservers = NULL;
  }
  if (qet_keyfiles != NULL)
  {
    for (i = 0; qet_keyfiles[i] != NULL; i++)
      free(qet_keyfiles[i]);
    free(qet_keyfiles);
    qet_keyfiles = NULL;
  }
}

/* fork/exec argv; optional stdin feed, optional stdout capture (malloc'd
 * into *out). Returns the child exit status, or -1 on spawn failure. */
static int qet_spawn
(
  char *const argv[],
  const char *input,
  char      **out
)
{
  int   inpipe[2]  = {-1, -1};
  int   outpipe[2] = {-1, -1};
  pid_t pid;
  int   status;

  if (input != NULL &&
      pipe(inpipe) != 0)
    return -1;
  if (out != NULL &&
      pipe(outpipe) != 0)
  {
    if (input != NULL)
    {
      close(inpipe[0]);
      close(inpipe[1]);
    }
    return -1;
  }

  pid = fork();
  if (pid < 0)
  {
    if (input != NULL)
    {
      close(inpipe[0]);
      close(inpipe[1]);
    }
    if (out != NULL)
    {
      close(outpipe[0]);
      close(outpipe[1]);
    }
    return -1;
  }
  if (pid == 0)
  {
    if (input != NULL)
    {
      dup2(inpipe[0], STDIN_FILENO);
      close(inpipe[0]);
      close(inpipe[1]);
    }
    if (out != NULL)
    {
      dup2(outpipe[1], STDOUT_FILENO);
      close(outpipe[0]);
      close(outpipe[1]);
    }
    execvp(argv[0], argv);
    _exit(127);
  }

  if (input != NULL)
  {
    close(inpipe[0]);
    /* child may have died; it is reaped below regardless */
    if (safe_write(inpipe[1], input, strlen(input)) < 0)
      (void)0;
    close(inpipe[1]);
  }
  if (out != NULL)
  {
    size_t  cap = 4096;
    size_t  len = 0;
    char   *buf = xmalloc(cap);
    ssize_t n;

    close(outpipe[1]);
    while ((n = read(outpipe[0], buf + len, cap - len - 1)) > 0)
    {
      len += (size_t)n;
      if (len + 1 >= cap)
      {
        cap *= 2;
        buf  = xrealloc(buf, cap);
      }
    }
    close(outpipe[0]);
    buf[len] = '\0';
    *out     = buf;
  }

  if (waitpid(pid, &status, 0) < 0)
    return -1;
  return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

/* assemble a gpg argv: "gpg" [--quiet --no-permission-warning] extra...
 * extra is a NULL-terminated list; result is NULL-terminated */
static void qet_gpg_argv
(
  char      **av,
  size_t      avlen,
  const char *first,
  ...
)
{
  va_list     ap;
  size_t      n = 0;
  const char *a;

  av[n++] = q_deconst("gpg");
  if (qet_quiet)
  {
    av[n++] = q_deconst("--quiet");
    av[n++] = q_deconst("--no-permission-warning");
  }
  if (first != NULL)
  {
    av[n++] = q_deconst(first);
    va_start(ap, first);
    while ((a = va_arg(ap, const char *)) != NULL &&
           n < avlen - 1)
      av[n++] = q_deconst(a);
    va_end(ap);
  }
  av[n] = NULL;
}

/* split a gpg --with-colons line in place; empty fields preserved
 * (strtok collapses them, which corrupts fixed-position field access) */
static int qet_colon_fields
(
  char  *line,
  char **fields,
  int    maxf
)
{
  int   nf = 0;
  char *p;

  fields[nf++] = line;
  for (p = line; *p != '\0' && nf < maxf; p++)
    if (*p == ':')
    {
      *p           = '\0';
      fields[nf++] = p + 1;
    }
  return nf;
}

static void qet_touch
(
  const char *path
)
{
  int fd = open(path, O_WRONLY | O_CREAT, 0644);

  if (fd >= 0)
  {
    futimens(fd, NULL);
    close(fd);
  }
}

static void qet_gpgconf_kill(void)
{
  char *av[] = {q_deconst("gpgconf"), q_deconst("--kill"), q_deconst("all"),
                NULL};

  (void)qet_spawn(av, NULL, NULL);
}

/* the WKD refresh: locate every imported key's UID email via WKD */
static void qet_wkd_locate(void)
{
  char  *av[8];
  char  *keys = NULL;
  char  *line;
  char  *sp;
  set   *emails;
  array *ekeys;
  size_t i;
  char  *e;
  char **loc;
  size_t nloc;

  qet_gpg_argv(av, 8, "--batch", "--with-colons", "--list-keys", NULL);
  if (qet_spawn(av, NULL, &keys) != 0 ||
      keys == NULL)
  {
    free(keys);
    return;
  }

  emails = create_set();
  for (line = strtok_r(keys, "\n", &sp);
       line != NULL;
       line = strtok_r(NULL, "\n", &sp))
  {
    char *fields[16];
    int   nf;
    char *lt;
    char *gt;
    char *at;

    if (strncmp(line, "uid:", 4) != 0)
      continue;
    nf = qet_colon_fields(line, fields, 16);
    if (nf < 10)
      continue;
    lt = strchr(fields[9], '<');
    if (lt == NULL)
      continue;
    gt = strchr(lt + 1, '>');
    if (gt == NULL)
      continue;
    *gt = '\0';
    at  = strchr(lt + 1, '@');
    if (at == NULL ||
        strchr(at + 1, '.') == NULL)
      continue;
    add_set(lt + 1, emails);
  }
  free(keys);

  ekeys = set_keys(emails);
  nloc  = array_cnt(ekeys);
  if (nloc == 0)
  {
    array_free(ekeys);
    free_set(emails);
    return;
  }

  loc         = xmalloc(sizeof(*loc) * (nloc + 6));
  nloc        = 0;
  loc[nloc++] = q_deconst("gpg");
  if (qet_quiet)
  {
    loc[nloc++] = q_deconst("--quiet");
    loc[nloc++] = q_deconst("--no-permission-warning");
  }
  loc[nloc++] = q_deconst("--auto-key-locate=clear,nodefault,wkd");
  loc[nloc++] = q_deconst("--locate-key");
  array_for_each(ekeys, i, e)
    loc[nloc++] = e;
  loc[nloc] = NULL;
  (void)qet_spawn(loc, NULL, NULL);
  free(loc);
  array_free(ekeys);
  free_set(emails);
}

/* fingerprints (fpr field 10) from `gpg --list-keys/--list-secret-keys`,
 * optionally excluding one; caller frees the returned set */
static set *qet_fingerprints
(
  bool        secret,
  const char *exclude
)
{
  char *av[8];
  char *out = NULL;
  char *line;
  char *sp;
  set  *fps = create_set();

  qet_gpg_argv(av, 8, "--batch", secret ? "--list-secret-keys" : "--list-keys",
               "--keyid-format=long", "--with-colons", NULL);
  if (qet_spawn(av, NULL, &out) != 0 ||
      out == NULL)
  {
    free(out);
    return fps;
  }
  for (line = strtok_r(out, "\n", &sp);
       line != NULL;
       line = strtok_r(NULL, "\n", &sp))
  {
    char *fields[16];
    int   nf;

    if (strncmp(line, "fpr:", 4) != 0)
      continue;
    nf = qet_colon_fields(line, fields, 16);
    if (nf < 10 ||
        fields[9][0] == '\0')
      continue;
    if (exclude != NULL &&
        strcmp(fields[9], exclude) == 0)
      continue;
    add_set(fields[9], fps);
  }
  free(out);
  return fps;
}

/* checking whether we can trust all newly added release keys.
 * every new key in it gets one that only root user can and should change
 * if it's writable by other users, we refuse to trust the key. */
static bool qet_keyfile_secure
(
  const char *path
)
{
  struct stat st;

  if (stat(path, &st) != 0)
    return true;

  if (!S_ISREG(st.st_mode))
  {
    warn("%s is not a regular file, refusing to trust its keys", path);
    return false;
  }
  if (st.st_uid != 0 &&
      st.st_uid != geteuid())
  {
    warn("%s is not owned by root, refusing to trust its keys", path);
    return false;
  }
  if ((st.st_mode & (S_IWGRP | S_IWOTH)) != 0)
  {
    warn("%s is writable by group or others, refusing to trust its keys", path);
    return false;
  }
  return true;
}

static int qet_refresh
(
  const char *lastrun
)
{
  struct stat     st;
  time_t          now;
  time_t          lst;
  char           *av[16];
  size_t          k;
  int             rc;
  struct timespec lts;
  struct timespec cts;
  struct timespec mts;
  bool            fresh;
  bool            newer;

  now         = time(NULL);
  lst         = 0;
  lts.tv_sec  = 0;
  lts.tv_nsec = 0;
  newer       = false;

  if (stat(lastrun, &st) == 0)
  {
    lst = st.st_mtime;
    lts = get_stat_mtime(&st);
  }
  fresh = now - 86400 < lst;

  for (k = 0; qet_keyfiles[k] != NULL; k++)
  {
    if (stat(qet_keyfiles[k], &st) != 0)
      continue;
    cts = get_stat_ctime(&st);
    mts = get_stat_mtime(&st);
    if (cts.tv_sec > lts.tv_sec ||
        (cts.tv_sec == lts.tv_sec &&
         cts.tv_nsec > lts.tv_nsec) ||
        mts.tv_sec > lts.tv_sec ||
        (mts.tv_sec == lts.tv_sec &&
         mts.tv_nsec > lts.tv_nsec))
      newer = true;
  }

  if (fresh &&
      !newer)
  {
    if (!qet_quiet)
      printf("GnuPG keyring for package signatures already "
             "up-to-date.\n");
    return 0;
  }
  if (!qet_quiet)
  {
    if (fresh)
      printf("Importing changed release key files\n");
    else
      printf("Updating GnuPG keyring for package signatures\n");
  }

  for (k = 0; qet_keyfiles[k] != NULL; k++)
  {
    if (!qet_keyfile_secure(qet_keyfiles[k]))
      return 1;
    qet_gpg_argv(av, 16, "--batch", "--import", qet_keyfiles[k], NULL);
    rc = qet_spawn(av, NULL, NULL);
    if (rc != 0)
    {
      warn("gpg --import %s failed", qet_keyfiles[k]);
      if (stat(qet_keyfiles[k], &st) == 0)
        warn("remove %s and run qetuto again", qet_home);
      return rc > 0 ? rc : 1;
    }
  }

  if (fresh)
    return 0;

  if (qet_external)
  {
    for (k = 0; qet_keyservers[k] != NULL; k++)
    {
      char  *tav[16];
      size_t n;

      n        = 0;
      tav[n++] = q_deconst("timeout");
      tav[n++] = q_deconst("-k");
      tav[n++] = q_deconst(QET_GPG_KILL);
      tav[n++] = q_deconst(QET_GPG_TERM);
      tav[n++] = q_deconst("gpg");
      if (qet_quiet)
      {
        tav[n++] = q_deconst("--quiet");
        tav[n++] = q_deconst("--no-permission-warning");
      }
      tav[n++] = q_deconst("--batch");
      tav[n++] = q_deconst("--keyserver");
      tav[n++] = (char *)qet_keyservers[k];
      tav[n++] = q_deconst("--refresh-keys");
      tav[n]   = NULL;
      (void)qet_spawn(tav, NULL, NULL);
    }

    qet_wkd_locate();
  }

  qet_touch(lastrun);
  return 0;
}

/* sign one release key with the local trust key, so gpg treats it as
 * trusted. this is the step that turns "the key is in the keyring" into
 * "packages signed with this key are accepted".
 * the passphrase of the local trust key is read from the pass file in
 * the keyring directory. the first gpg call is the normal way, the
 * second one is the same thing asked differently, for the gpg versions
 * where the first refuses. if both fail nothing is signed and the check
 * after us reports the key as not trusted. */
static void qet_lsign
(
  char *fp
)
{
  char   passfile[_Q_PATH_MAX + 16];
  char  *av[18];
  size_t n;

  snprintf(passfile, sizeof(passfile), "%s/pass", qet_home);

  n       = 0;
  av[n++] = q_deconst("gpg");
  if (qet_quiet)
  {
    av[n++] = q_deconst("--quiet");
    av[n++] = q_deconst("--no-permission-warning");
  }
  av[n++] = q_deconst("--batch");
  av[n++] = q_deconst("--yes");
  av[n++] = q_deconst("--no-tty");
  av[n++] = q_deconst("--passphrase-file");
  av[n++] = passfile;
  av[n++] = q_deconst("--pinentry-mode");
  av[n++] = q_deconst("loopback");
  av[n++] = q_deconst("--quick-lsign-key");
  av[n++] = fp;
  av[n]   = NULL;
  if (qet_spawn(av, NULL, NULL) == 0)
    return;

  n       = 0;
  av[n++] = q_deconst("gpg");
  if (qet_quiet)
  {
    av[n++] = q_deconst("--quiet");
    av[n++] = q_deconst("--no-permission-warning");
  }
  av[n++] = q_deconst("--command-fd");
  av[n++] = q_deconst("0");
  av[n++] = q_deconst("--yes");
  av[n++] = q_deconst("--no-tty");
  av[n++] = q_deconst("--passphrase-file");
  av[n++] = passfile;
  av[n++] = q_deconst("--pinentry-mode");
  av[n++] = q_deconst("loopback");
  av[n++] = q_deconst("--lsign-key");
  av[n++] = fp;
  av[n]   = NULL;
  (void)qet_spawn(av, "y\ny\n", NULL);
}

/* the keyring check, done on every run, before anything is changed.
 * first step, check: list the keys in the keyring and the keys in the release
 * key file(s) and compare. only a read.
 * second step, act on what the check found, and only then:
 *   repair 2: a key of a file is not in the keyring -> import that file,
 *             then start again with repair 1.
 *   repair 1 and 2: a key is in the keyring but not trusted -> sign it
 *             with the local trust key, then start again with repair 0.
 *   repair 0: change nothing, only report.
 * an expired or revoked release key is fine.
 * if something is still wrong after that, the run fails and says what:
 *   - there is no local trust key
 *   - a key could not be imported or signed
 *   - a key file can be changed by someone other than root
 *   - gpg cannot read the keyring
 * the fix is then to remove the keyring directory and run qetuto again. */
static int qet_verify
(
  int repair
)
{
  char  *av[16];
  char  *fields[16];
  char  *out;
  char  *line;
  char  *sp;
  set   *valid;
  set   *present;
  size_t k;
  int    nf;
  int    bad;
  int    lsigned;
  int    imported;
  char   val;
  bool   primary;
  bool   ultimate;
  bool   tried;

  out      = NULL;
  valid    = create_set();
  present  = create_set();
  bad      = 0;
  lsigned  = 0;
  imported = 0;
  val      = '\0';
  primary  = false;
  ultimate = false;

  qet_gpg_argv(av, 16, "--no-permission-warning", "--batch", "--with-colons",
               "--list-keys", NULL);
  if (qet_spawn(av, NULL, &out) != 0 ||
      out == NULL)
  {
    free(out);
    free_set(valid);
    free_set(present);
    warn("gpg cannot read the keyring in %s", qet_home);
    warn("remove %s and run qetuto again", qet_home);
    return 1;
  }
  for (line = strtok_r(out, "\n", &sp);
       line != NULL;
       line = strtok_r(NULL, "\n", &sp))
  {
    if (strncmp(line, "pub:", 4) == 0)
    {
      nf      = qet_colon_fields(line, fields, 16);
      val     = nf > 1 ? fields[1][0] : '\0';
      primary = true;
    }
    else if (primary &&
             strncmp(line, "fpr:", 4) == 0)
    {
      primary = false;
      nf      = qet_colon_fields(line, fields, 16);
      if (nf < 10 ||
          val == '\0')
        continue;
      if (val == 'u')
        ultimate = true;
      if (strchr("fuer", val) != NULL)
        add_set(fields[9], valid);
      add_set(fields[9], present);
    }
  }
  free(out);

  if (!ultimate)
  {
    warn("no local trust key in %s", qet_home);
    bad++;
    repair = 0;
  }

  for (k = 0; qet_keyfiles[k] != NULL; k++)
  {
    out     = NULL;
    primary = false;
    tried   = false;
    if (!qet_keyfile_secure(qet_keyfiles[k]))
    {
      bad++;
      continue;
    }
    qet_gpg_argv(av, 16, "--no-permission-warning", "--batch", "--with-colons",
                 "--show-keys", qet_keyfiles[k], NULL);
    if (qet_spawn(av, NULL, &out) != 0 ||
        out == NULL)
    {
      warn("cannot read the keys of %s", qet_keyfiles[k]);
      bad++;
      free(out);
      continue;
    }
    for (line = strtok_r(out, "\n", &sp);
         line != NULL;
         line = strtok_r(NULL, "\n", &sp))
    {
      if (strncmp(line, "pub:", 4) == 0)
      {
        primary = true;
      }
      else if (primary &&
               strncmp(line, "fpr:", 4) == 0)
      {
        primary = false;
        nf      = qet_colon_fields(line, fields, 16);
        if (nf < 10 ||
            contains_set(fields[9], valid) != NULL)
          continue;
        if (repair == 2 &&
            contains_set(fields[9], present) == NULL)
        {
          if (!tried)
          {
            char *iav[16];

            if (!qet_quiet)
              printf("Importing release keys from %s\n", qet_keyfiles[k]);
            qet_gpg_argv(iav, 16, "--batch", "--import", qet_keyfiles[k], NULL);
            (void)qet_spawn(iav, NULL, NULL);
            tried = true;
          }
          imported++;
          continue;
        }
        if (repair > 0 &&
            contains_set(fields[9], present) != NULL)
        {
          if (!qet_quiet)
            printf("Signing release key %s with the local trust key\n",
                   fields[9]);
          qet_lsign(fields[9]);
          lsigned++;
          continue;
        }
        warn("release key %s is not trusted in %s", fields[9], qet_home);
        bad++;
      }
    }
    free(out);
  }
  free_set(valid);
  free_set(present);

  if (lsigned > 0)
  {
    qet_gpg_argv(av, 16, "--no-permission-warning", "--batch",
                 "--check-trustdb", NULL);
    (void)qet_spawn(av, NULL, NULL);
  }
  if (imported > 0)
    return qet_verify(1);
  if (lsigned > 0)
    return qet_verify(0);

  if (bad > 0)
  {
    warn("remove %s and run qetuto again", qet_home);
    return 1;
  }
  return 0;
}

static int qet_bootstrap
(
  const char *lastrun
)
{
  char        staging[_Q_PATH_MAX + 16];
  char        orig[_Q_PATH_MAX];
  char        path[_Q_PATH_MAX + 32];
  char       *rmav[4];
  char       *av[24];
  FILE       *f;
  char       *pass    = NULL;
  char       *mykeyid = NULL;
  set        *relkeys;
  array      *relarr;
  size_t      i;
  char       *fp;
  struct stat st;

  snprintf(orig, sizeof(orig), "%s", qet_home);
  snprintf(staging, sizeof(staging), "%s.getuto.tmp", qet_home);

  rmav[0] = q_deconst("rm");
  rmav[1] = q_deconst("-rf");
  rmav[2] = staging;
  rmav[3] = NULL;
  (void)qet_spawn(rmav, NULL, NULL);

  if (mkdir_p(staging, 0755) != 0)
  {
    warnp("cannot create %s", staging);
    return 1;
  }
  chmod(staging, 0755);
  setenv("GNUPGHOME", staging, 1);

  strcpy(path, staging);
  strcat(path, "/dirmngr.conf");
  f = fopen(path, "w");
  if (f != NULL)
  {
    fputs("honor-http-proxy\nno-use-tor\nstandard-resolver\n"
          "resolver-timeout 90\nconnect-timeout 90\n",
          f);
    fclose(f);
  }
  strcpy(path, staging);
  strcat(path, "/gpg-agent.conf");
  f = fopen(path, "w");
  if (f != NULL)
  {
    fputs("disable-scdaemon\n", f);
    fclose(f);
  }
  strcpy(path, staging);
  strcat(path, "/gpg.conf");
  f = fopen(path, "w");
  if (f != NULL)
  {
    fputs("no-greeting\n", f);
    fclose(f);
  }

  {
    char *oav[] = {q_deconst("openssl"), q_deconst("rand"),
                   q_deconst("-base64"), q_deconst("32"), NULL};

    if (qet_spawn(oav, NULL, &pass) != 0 ||
        pass == NULL)
    {
      warn("could not generate a passphrase (openssl)");
      goto fail;
    }
    rmspace(pass);
  }

  {
    char  keycfg[_Q_PATH_MAX + 48];
    char *cfgbuf;
    int   fd;

    strcpy(keycfg, staging);
    strcat(keycfg, "/.keycfg.XXXXXX");
    fd = mkstemp(keycfg);
    if (fd < 0)
    {
      warnp("mkstemp failed");
      goto fail;
    }
    fchmod(fd, 0600);
    cfgbuf =
        xasprintf("%%echo Generating Portage local OpenPGP trust key\n"
                  "Key-Type: RSA\nKey-Length: 3072\n"
                  "Subkey-Type: RSA\nSubkey-Length: 3072\n"
                  "Name-Real: Portage Local Trust Key\n"
                  "Name-Comment: local signing only\n"
                  "Name-Email: portage@localhost\n"
                  "Expire-Date: 0\nPassphrase: %s\n%%commit\n%%echo done\n",
                  pass);
    if (safe_write(fd, cfgbuf, strlen(cfgbuf)) < 0)
      warnp("writing key config");
    close(fd);
    free(cfgbuf);

    qet_gpg_argv(av, 24, "--batch", "--generate-key", keycfg, NULL);
    if (qet_spawn(av, NULL, NULL) != 0)
    {
      unlink(keycfg);
      warn("gpg --generate-key failed");
      goto fail;
    }
    unlink(keycfg);
  }

  strcpy(path, staging);
  strcat(path, "/pass");
  f = fopen(path, "w");
  if (f == NULL)
  {
    warnp("cannot write %s", path);
    goto fail;
  }
  chmod(path, 0600);
  fprintf(f, "%s\n", pass);
  fclose(f);

  {
    set   *my = qet_fingerprints(true, NULL);
    array *mk = set_keys(my);

    if (array_cnt(mk) > 0)
      mykeyid = xstrdup((char *)array_get(mk, 0));
    array_free(mk);
    free_set(my);
  }
  if (mykeyid == NULL)
  {
    warn("could not determine local trust key fingerprint");
    goto fail;
  }
  strcpy(path, staging);
  strcat(path, "/mykeyid");
  f = fopen(path, "w");
  if (f != NULL)
  {
    fprintf(f, "%s\n", mykeyid);
    fclose(f);
  }

  {
    size_t kf;
    int    imported = 0;

    for (kf = 0; qet_keyfiles[kf] != NULL; kf++)
    {
      if (stat(qet_keyfiles[kf], &st) != 0)
        continue;
      if (!qet_keyfile_secure(qet_keyfiles[kf]))
        goto fail;
      qet_gpg_argv(av, 24, "--batch", "--import", qet_keyfiles[kf], NULL);
      if (qet_spawn(av, NULL, NULL) == 0)
        imported++;
    }
    if (imported == 0)
    {
      warn("no release keyring found (checked %s). Is "
           "sec-keys/openpgp-keys-gentoo-release installed?",
           qet_keyfiles[0]);
      goto fail;
    }
  }

  relkeys = qet_fingerprints(false, mykeyid);
  relarr  = set_keys(relkeys);

  if (qet_external)
  {
    for (size_t k = 0; qet_keyservers[k] != NULL; k++)
    {
      char  *tav[64];
      size_t n = 0;

      tav[n++] = q_deconst("timeout");
      tav[n++] = q_deconst("-k");
      tav[n++] = q_deconst(QET_GPG_KILL);
      tav[n++] = q_deconst(QET_GPG_TERM);
      tav[n++] = q_deconst("gpg");
      if (qet_quiet)
      {
        tav[n++] = q_deconst("--quiet");
        tav[n++] = q_deconst("--no-permission-warning");
      }
      tav[n++] = q_deconst("--batch");
      tav[n++] = q_deconst("--keyserver");
      tav[n++] = (char *)qet_keyservers[k];
      tav[n++] = q_deconst("--recv-keys");
      array_for_each(relarr, i, fp)
        if (n < 62)
          tav[n++] = fp;
      tav[n] = NULL;
      (void)qet_spawn(tav, NULL, NULL);
    }

    qet_wkd_locate();
  }

  {
    char passfile[_Q_PATH_MAX + 48];

    strcpy(passfile, staging);
    strcat(passfile, "/pass");
    array_for_each(relarr, i, fp)
    {
      char  *lav[16];
      size_t n = 0;

      lav[n++] = q_deconst("gpg");
      if (qet_quiet)
      {
        lav[n++] = q_deconst("--quiet");
        lav[n++] = q_deconst("--no-permission-warning");
      }
      lav[n++] = q_deconst("--batch");
      lav[n++] = q_deconst("--yes");
      lav[n++] = q_deconst("--no-tty");
      lav[n++] = q_deconst("--passphrase-file");
      lav[n++] = passfile;
      lav[n++] = q_deconst("--pinentry-mode");
      lav[n++] = q_deconst("loopback");
      lav[n++] = q_deconst("--quick-lsign-key");
      lav[n++] = fp;
      lav[n]   = NULL;
      if (qet_spawn(lav, NULL, NULL) != 0)
      {
        char  *fav[18];
        size_t m = 0;

        fav[m++] = q_deconst("gpg");
        if (qet_quiet)
        {
          fav[m++] = q_deconst("--quiet");
          fav[m++] = q_deconst("--no-permission-warning");
        }
        fav[m++] = q_deconst("--command-fd");
        fav[m++] = q_deconst("0");
        fav[m++] = q_deconst("--yes");
        fav[m++] = q_deconst("--no-tty");
        fav[m++] = q_deconst("--passphrase-file");
        fav[m++] = passfile;
        fav[m++] = q_deconst("--pinentry-mode");
        fav[m++] = q_deconst("loopback");
        fav[m++] = q_deconst("--lsign-key");
        fav[m++] = fp;
        fav[m]   = NULL;
        (void)qet_spawn(fav, "y\ny\n", NULL);
      }
    }
  }
  array_free(relarr);
  free_set(relkeys);

  qet_gpg_argv(av, 24, "--batch", "--check-trustdb", NULL);
  (void)qet_spawn(av, NULL, NULL);

  strcpy(path, staging);
  strcat(path, "/trustdb.gpg");
  chmod(path, 0644);

  qet_gpgconf_kill();

  if (rename(staging, orig) != 0)
  {
    warnp("cannot move %s into place", staging);
    goto fail;
  }
  setenv("GNUPGHOME", orig, 1);

  qet_touch(lastrun);

  free(pass);
  free(mykeyid);
  return 0;

fail:
  free(pass);
  free(mykeyid);
  qet_gpgconf_kill();
  rmav[2] = staging;
  (void)qet_spawn(rmav, NULL, NULL);
  return 1;
}

/* everything qetuto does to the keyring: create it or refresh it, then
 * the keyring check verification. returns 0 when the keyring is good,
 * something else when not. */
static int qet_work(void)
{
  int         ret;
  char        lastrun[_Q_PATH_MAX + 16];
  char        trustdb[_Q_PATH_MAX + 16];
  struct stat st;

  snprintf(lastrun, sizeof(lastrun), "%s/.getuto.last", qet_home);

  qet_build_lists();

  qet_gpgconf_kill();

  if (stat(qet_home, &st) != 0)
  {
    if (!qet_quiet)
      printf("Initializing %s\n", qet_home);
    ret = qet_bootstrap(lastrun);
  }
  else
  {
    setenv("LC_ALL", "C.UTF-8", 1);
    ret = qet_refresh(lastrun);
  }

  snprintf(trustdb, sizeof(trustdb), "%s/trustdb.gpg", qet_home);
  if (chmod(trustdb, 0644) != 0 &&
      ret == 0)
  {
    warnp("cannot access %s", trustdb);
    ret = 1;
  }
  if (ret == 0)
    ret = qet_verify(2);

  qet_gpgconf_kill();
  qet_free_lists();
  return ret;
}

static volatile sig_atomic_t qet_child;

static void qet_forward
(
  int sig
)
{
  (void)sig;
  if (qet_child > 0)
    kill(-(pid_t)qet_child, SIGTERM);
}

/* QETUTO_NONFATAL=1: never let a keyring problem stop emerge/qmerge.
 * emerge stops when its trust helper returns anything but 0, so here
 * the work runs in a child process and so we can continue watching it:
 *   - the child reports a problem      -> we say so and return 0
 *   - the child crashes                -> we say so and return 0
 *   - the child takes longer than QETUTO_TIMEOUT seconds
 *                                      -> we stop it, say so, return 0
 * we 'presume' this is safe: the keyring decides which signatures are accepted,
 * a package whose signature cannot be verified is still refused later
 * so from the post-run verifications we are covered thanks to q/emerge. */
static int qet_supervise(void)
{
  struct sigaction sa;
  struct timespec  nap;
  char             staging[_Q_PATH_MAX + 16];
  time_t           deadline;
  long             limit;
  pid_t            pid;
  pid_t            w;
  int              status;
  int              i;
  bool             late;

  limit = 0;
  if (qetuto_timeout_conf != NULL)
    limit = strtol(qetuto_timeout_conf, NULL, 10);
  if (limit <= 0)
    limit = 120;
  /* the keyserver calls have their own limit of up to 2.5 minutes each
   * and the WKD lookup comes after them. we thus let them be. */
  if (qet_external)
  {
    i = 0;
    if (qetuto_keyservers_conf != NULL &&
        qetuto_keyservers_conf[0] != '\0')
    {
      char **srv;

      srv = qet_split_list(qetuto_keyservers_conf);
      while (srv[i] != NULL)
        free(srv[i++]);
      free(srv);
    }
    else
    {
      while (qet_keyservers_default[i] != NULL)
        i++;
    }
    limit += 150L * i + 150;
  }
  status      = 0;
  late        = false;
  w           = 0;
  nap.tv_sec  = 0;
  nap.tv_nsec = 50000000;

  fflush(NULL);
  pid = fork();
  if (pid < 0)
  {
    warnp("the binary package keyring was not updated (cannot fork)");
    return 0;
  }
  if (pid == 0)
  {
    setpgid(0, 0);
    status = qet_work();
    fflush(NULL);
    _exit(status);
  }

  setpgid(pid, pid);
  qet_child = pid;
  VAL_CLEAR(sa);
  sa.sa_handler = qet_forward;
  sigemptyset(&sa.sa_mask);
  sigaction(SIGINT, &sa, NULL);
  sigaction(SIGTERM, &sa, NULL);

  deadline = time(NULL) + limit;
  for (;;)
  {
    w = waitpid(pid, &status, WNOHANG);
    if (w == pid)
      break;
    if (w < 0 &&
        errno != EINTR)
      break;
    if (time(NULL) >= deadline)
    {
      late = true;
      kill(-pid, SIGTERM);
      for (i = 0; i < 40; i++)
      {
        w = waitpid(pid, &status, WNOHANG);
        if (w == pid)
          break;
        nanosleep(&nap, NULL);
      }
      if (w != pid)
      {
        kill(-pid, SIGKILL);
        w = waitpid(pid, &status, 0);
      }
      break;
    }
    nanosleep(&nap, NULL);
  }
  qet_child = 0;

  if (!late &&
      w == pid &&
      WIFEXITED(status) &&
      WEXITSTATUS(status) == 0)
    return 0;

  qet_gpgconf_kill();
  snprintf(staging, sizeof(staging), "%s.getuto.tmp", qet_home);
  setenv("GNUPGHOME", staging, 1);
  qet_gpgconf_kill();
  setenv("GNUPGHOME", qet_home, 1);

  if (late)
    warn("the binary package keyring was not updated "
         "(took longer than %ld seconds)",
         limit);
  else if (w == pid &&
           WIFSIGNALED(status))
    warn("the binary package keyring was not updated "
         "(stopped by signal %d)",
         WTERMSIG(status));
  else if (w == pid &&
           WIFEXITED(status))
    warn("the binary package keyring was not updated "
         "(exit code %d)",
         WEXITSTATUS(status));
  else
    warn("the binary package keyring was not updated");
  warn("continuing, signed binary packages may be refused");
  return 0;
}

int qetuto_main
(
  int    argc,
  char **argv
)
{
  int    ret;
  size_t rl;

  while ((ret = GETOPT_LONG(QETUTO, qetuto, "")) != -1)
  {
    switch (ret)
    {
      COMMON_GETOPTS_CASES(qetuto)
    }
  }

  qet_quiet    = verbose == 0;
  qet_external = qetuto_external_refresh_conf !=
                 NULL &&
                 strcmp(qetuto_external_refresh_conf, "1") == 0;

  qet_root = xstrdup(portroot);
  rl       = strlen(qet_root);
  while (rl > 1 &&
         qet_root[rl - 1] == '/')
    qet_root[--rl] = '\0';
  if (strcmp(qet_root, "/") == 0)
    qet_root[0] = '\0';

  if (geteuid() != 0 &&
      qet_root[0] == '\0')
    err("qetuto must be run as root");

  snprintf(qet_home, sizeof(qet_home), "%s/etc/portage/gnupg", qet_root);
  setenv("GNUPGHOME", qet_home, 1);

  if (qetuto_nonfatal_conf != NULL &&
      strcmp(qetuto_nonfatal_conf, "1") == 0)
    ret = qet_supervise();
  else
    ret = qet_work();

  free(qet_root);
  qet_root = NULL;
  return ret;
}

/* vim: set ts=2 sw=2 expandtab cino+=\:0 foldmethod=marker: */
