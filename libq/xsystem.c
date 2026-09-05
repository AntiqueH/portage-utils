/*
 * Copyright 2010-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2010-2016 Mike Frysinger  - <vapier@gentoo.org>
 * Copyright 2022-     Fabian Groffen  - <grobian@gentoo.org>
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 */

#include "main.h"

#include <stdlib.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <sys/types.h>
#include <unistd.h>
#include <xalloc.h>

#include "xsystem.h"

int xsystembash_status
(
  const char  *command,
  const char **argv,
  int          cwd
)
{
  pid_t p;
  int   status;

  /* warn once when the preferred shell is absent: the /bin/sh fallback
   * below cannot source bash-serialized environments, so phase
   * execution is degraded */
  if (argv == NULL)
  {
    static bool bash_warned = false;

    if (!bash_warned &&
        access(CONFIG_EPREFIX "bin/bash", X_OK) != 0)
    {
      warn("%sbin/bash not found, falling back to /bin/sh "
           "(degraded script execution)", CONFIG_EPREFIX);
      bash_warned = true;
    }
  }

  p = fork();
  switch (p) {
  case 0: /* child */
    if (cwd != AT_FDCWD)
    {
      if (fchdir(cwd))
      {
        /* fchdir works with O_PATH starting w/linux-3.5 */
        if (errno == EBADF)
        {
          char path[_Q_PATH_MAX];
          snprintf(path, sizeof(path), "/proc/self/fd/%i", cwd);
          if (chdir(path))
            errp("chdir(%s) failed", path);
        }
        else
        {
          errp("fchdir(%i) failed", cwd);
        }
      }
    }
    if (argv == NULL)
    {
      execl(CONFIG_EPREFIX "bin/bash",
            "bash",
            "--norc",
            "--noprofile",
            "-c", command,
            (char *)NULL);
      /* Hrm, still here ?  Maybe no bash ... */
      _exit(execl("/bin/sh", "sh", "-c", command, (char *)NULL));
    }
    else
    {
      /* a straight argument vector, not a shell command line:
       * execute it directly; passing it through `bash -c` would
       * run argv[0] only, with the rest as positional params */
      _exit(execvp(argv[0], q_deconst_p(argv)));
    }

  default: /* parent */
    waitpid(p, &status, 0);
    if (WIFSIGNALED(status))
    {
      err("phase crashed with signal %i: %s", WTERMSIG(status),
          strsignal(WTERMSIG(status)));
    }
    else if (WIFEXITED(status))
    {
      return WEXITSTATUS(status);
    }
    /* fall through */

  case -1: /* fucked */
    errp("xsystembash(%s) failed", command);
  }
  return -1;
}

/* historic strict wrapper: any nonzero exit is fatal */
void xsystembash
(
  const char  *command,
  const char **argv,
  int          cwd
)
{
  int status = xsystembash_status(command, argv, cwd);

  if (status != 0)
    err("phase exited %i", status);
}

/* vim: set ts=2 sw=2 expandtab cino+=\:0 foldmethod=marker: */
