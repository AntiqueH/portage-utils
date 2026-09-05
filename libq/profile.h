/*
 * Copyright 2005-2019 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 */

#ifndef PROFILE_H
#define PROFILE_H 1

typedef void *(q_profile_callback_t)(void *, char *);
void *q_profile_follow(
		const char *file, q_profile_callback_t callback,
		void *data);

#endif
