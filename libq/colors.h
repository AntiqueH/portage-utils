/*
 * Copyright 2005-2021 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2019-     Fabian Groffen  - <grobian@gentoo.org>
 */

#ifndef COLORS_H
#define COLORS_H 1

extern const char *BOLD;
extern const char *NORM;
extern const char *BLUE;
extern const char *DKBLUE;
extern const char *CYAN;
extern const char *GREEN;
extern const char *DKGREEN;
extern const char *MAGENTA;
extern const char *RED;
extern const char *YELLOW;
extern const char *BRYELLOW;
extern const char *WHITE;

void color_remap(void);
void color_clear(void);
void color_suppress(void);
void color_unsuppress(void);

#endif
