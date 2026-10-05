/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * strtok_r for the memory sanitizer run of the fuzz targets.
 *
 */

#include <string.h>

char *strtok_r
(
  char       *s,
  const char *delim,
  char      **save
)
{
  char *end;

  if (s == NULL)
    s = *save;
  s += strspn(s, delim);
  if (*s == '\0')
  {
    *save = s;
    return NULL;
  }
  end = s + strcspn(s, delim);
  if (*end != '\0')
    *end++ = '\0';
  *save = end;
  return s;
}
