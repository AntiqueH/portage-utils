/*
 * Copyright 2011-2019 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2011-2016 Mike Frysinger  - <vapier@gentoo.org>
 * Copyright 2017-     Fabian Groffen  - <grobian@gentoo.org>
 */

#include "main.h"

#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <dirent.h>
#include <fcntl.h>
#include <xalloc.h>

#include "xmkdir.h"

/* Emulate `mkdir -p -m MODE PATH` */
int
mkdir_p_at(int dfd, const char *path, mode_t mode)
{
	char *_p;
	char *p;
	char *s;
	int ret;

	/* Assume that most of the time, only the last element
	 * is missing.  So if we can mkdir it right away, bail. */
	if (mkdirat(dfd, path, mode) == 0 || errno == EEXIST)
		return 0;

	/* Build up the whole tree */
	_p = p = xstrdup(path);
	ret = 0;

	while (*p) {
		/* Skip duplicate slashes */
		while (*p == '/')
			++p;

		/* Find the next path element */
		s = strchr(p, '/');
		if (!s) {
			if (mkdirat(dfd, _p, mode) != 0 && errno != EEXIST)
				ret = -1;
			break;
		}

		/* Make it */
		*s = '\0';
		if (mkdirat(dfd, _p, mode) != 0 && errno != EEXIST)
			ret = -1;
		*s = '/';

		p = s;
	}

	free(_p);

	return ret;
}

int
mkdir_p(const char *path, mode_t mode)
{
	return mkdir_p_at(AT_FDCWD, path, mode);
}

/* open directory NAME under DFD, creating it with MODE if missing, and
 * refuse to trust it just because it exists: mkdir_p() accepts any
 * existing directory, even one somebody else planted beforehand, and we
 * extract images and run root scripts in these.
 * a symlink or a file in its place is an error. as root, give it to
 * UID:GID (like portage does with the portage account), add MODE's bits,
 * strip world write, and warn when the previous owner was neither root
 * nor UID or the directory was world-writable. not root: refuse only a
 * world-writable directory that is not ours.
 * returns an fd. whoever calls this then works through that fd (openat,
 * mkdirat, fchdir), not through the path due to the fact that a path
 * can be re-pointed by a rename.. */
int
secure_dir_at
(
  int         dfd,
  const char *name,
  mode_t      mode,
  uid_t       uid,
  gid_t       gid,
  int        *outfd
)
{
  struct stat st;
  mode_t      want;
  int         fd;
  bool        created;

  created = mkdirat(dfd, name, mode) == 0;
  if (!created &&
      errno != EEXIST)
    return -1;
  fd = openat(dfd, name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
  if (fd < 0)
    return -1;
  if (fstat(fd, &st) != 0)
  {
    close(fd);
    return -1;
  }
  want = ((st.st_mode & 07777) | mode) & ~(mode_t)S_IWOTH;
  if (geteuid() == 0)
  {
    if (!created &&
        st.st_uid != 0 &&
        st.st_uid != uid)
      warn("repaired %s: owned by uid %u gid %u, mode %04o",
           name, (unsigned)st.st_uid, (unsigned)st.st_gid,
           (unsigned)(st.st_mode & 07777));
    else if (!created &&
        (st.st_mode & S_IWOTH))
      warn("repaired %s: world-writable, mode %04o",
           name, (unsigned)(st.st_mode & 07777));
    if ((st.st_uid != uid ||
        st.st_gid != gid) &&
        fchown(fd, uid, gid) != 0)
    {
      close(fd);
      return -1;
    }
    if ((st.st_mode & 07777) != want &&
        fchmod(fd, want) != 0)
    {
      close(fd);
      return -1;
    }
  }
  else if (st.st_uid != geteuid() &&
      (st.st_mode & S_IWOTH))
  {
    close(fd);
    errno = EACCES;
    return -1;
  }
  *outfd = fd;
  return 0;
}

/* Emulate `rm -rf PATH` */
int
rm_rf_at(int dfd, const char *path)
{
	int subdfd;
	DIR *dir;
	struct dirent *de;
	int ret = 0;

	/* Cannot use O_PATH as we want to use fdopendir() */
	subdfd = openat(dfd, path, O_RDONLY|O_CLOEXEC|O_NOFOLLOW);
	if (subdfd < 0)
		return -1;

	dir = fdopendir(subdfd);
	if (!dir) {
		close(subdfd);
		return unlinkat(dfd, path, 0);
	}

	while ((de = readdir(dir)) != NULL) {
		if (strcmp(de->d_name, ".") == 0 ||
				strcmp(de->d_name, "..") == 0)
			continue;
		if (unlinkat(subdfd, de->d_name, 0) == -1) {
			if (unlikely(errno != EISDIR)) {
				struct stat st;
				/* above is a linux short-cut, we really just want to
				 * know whether we're really with a directory or not */
				if (fstatat(subdfd, de->d_name, &st, 0) != 0 ||
						!(st.st_mode & S_IFDIR))
					errp("could not unlink %s", de->d_name);
			}
			ret |= rm_rf_at(subdfd, de->d_name);
		}
	}

	ret |= unlinkat(dfd, path, AT_REMOVEDIR);

	/* this also does close(subdfd); */
	closedir(dir);

	return ret;
}

int
rm_rf(const char *path)
{
	return rm_rf_at(AT_FDCWD, path);
}

int
rmdir_r_at(int dfd, const char *path)
{
	size_t len;
	char *p;
	char *e;

	p = xstrdup(path);
	len = strlen(p);
	e = p + len;

	while (e != p) {
		if (unlinkat(dfd, p, AT_REMOVEDIR) && errno == ENOTEMPTY)
			break;
		while (*e != '/' && e > p)
			--e;
		*e = '\0';
	}

	free(p);

	return 0;
}

int
rmdir_r(const char *path)
{
	return rmdir_r_at(AT_FDCWD, path);
}
