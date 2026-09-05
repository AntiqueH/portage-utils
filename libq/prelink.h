/*
 * Copyright 2005-2019 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 */

#ifndef PRELINK_H
#define PRELINK_H 1

#include <stdbool.h>

bool prelink_available(void);
int hash_cb_prelink_undo(int fd, const char *filename);

#endif
