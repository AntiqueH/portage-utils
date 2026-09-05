/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 * 
 * GnuPG signing library (to be used as engine).
 * The whole idea came from cloning gpkg signing designs, of course.
 * Spawns BINPKG_GPG_SIGNING_BASE_COMMAND with the [PORTAGE_CONFIG]
 * substitution and streams data through the child.
 * Called & used by qgpkg-sign and the build-time signing functions in qpkg.
 * 
 */

#include "main.h"
#include "applets.h"

#include <errno.h>
#include <poll.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <xalloc.h>

#include "gpgsign.h"
#include "xasprintf.h"


/* we need docs on this implementation */
bool
gpgsign_vars_ok(void)
{
	if (binpkg_gpg_signing_gpg_home == NULL ||
			binpkg_gpg_signing_gpg_home[0] == '\0') {
		warn("BINPKG_GPG_SIGNING_GPG_HOME is not set");
		return false;
	}
	if (binpkg_gpg_signing_key == NULL ||
			binpkg_gpg_signing_key[0] == '\0') {
		warn("BINPKG_GPG_SIGNING_KEY is not set");
		return false;
	}
	if (binpkg_gpg_signing_base_command == NULL ||
			binpkg_gpg_signing_base_command[0] == '\0') {
		warn("GnuPG signing command is not set");
		return false;
	}
	return true;
}

static char *
gpgsign_command(bool detached)
{
	char       *cfg;
	char       *cmd;
	char       *w;
	const char *r;
	const char *p;
	size_t      n;
	size_t      len;

	xasprintf(&cfg, "--homedir %s --digest-algo %s --local-user %s "
			"%s --batch --no-tty",
			binpkg_gpg_signing_gpg_home,
			binpkg_gpg_signing_digest,
			binpkg_gpg_signing_key,
			detached ? "--detach-sig" : "--clear-sign");

	n = 0;
	for (r = binpkg_gpg_signing_base_command;
			(p = strstr(r, "[PORTAGE_CONFIG]")) != NULL;
			r = p + sizeof("[PORTAGE_CONFIG]") - 1)
		n++;
	len = strlen(binpkg_gpg_signing_base_command) + n * strlen(cfg) + 1;
	cmd = xmalloc(len);
	w = cmd;
	for (r = binpkg_gpg_signing_base_command;
			(p = strstr(r, "[PORTAGE_CONFIG]")) != NULL;
			r = p + sizeof("[PORTAGE_CONFIG]") - 1) {
		memcpy(w, r, p - r);
		w += p - r;
		memcpy(w, cfg, strlen(cfg));
		w += strlen(cfg);
	}
	strcpy(w, r);
	free(cfg);
	return cmd;
}

static void
gpgsign_append(char **buf, size_t *len, size_t *cap,
		const char *data, size_t n)
{
	if (*len + n + 1 > *cap) {
		*cap = (*cap == 0 ? 4096 : *cap * 2);
		while (*len + n + 1 > *cap)
			*cap *= 2;
		*buf = xrealloc(*buf, *cap);
	}
	memcpy(*buf + *len, data, n);
	*len += n;
	(*buf)[*len] = '\0';
}

static void
gpgsign_drain(struct gpgsign *g, int timeout)
{
	struct pollfd pfd[2];
	char          rbuf[BUFSIZ];
	ssize_t       rd;
	int           i;

	pfd[0].fd = g->out;
	pfd[1].fd = g->err;
	pfd[0].events = pfd[1].events = POLLIN;
	if (poll(pfd, 2, timeout) <= 0)
		return;
	for (i = 0; i < 2; i++) {
		if (pfd[i].fd == -1 ||
				!(pfd[i].revents & (POLLIN | POLLHUP | POLLERR)))
			continue;
		rd = read(pfd[i].fd, rbuf, sizeof(rbuf));
		if (rd > 0) {
			if (i == 0)
				gpgsign_append(&g->obuf, &g->olen, &g->ocap, rbuf, rd);
			else
				gpgsign_append(&g->ebuf, &g->elen, &g->ecap, rbuf, rd);
		} else if (rd == 0) {
			close(pfd[i].fd);
			if (i == 0)
				g->out = -1;
			else
				g->err = -1;
			pfd[i].fd = -1;
		}
	}
}

int
gpgsign_start(bool detached, struct gpgsign *g)
{
	char       *cmd;
	char      **argv;
	int         argc;
	int         inp[2];
	int         outp[2];
	int         errp[2];
	const char *tty;

	memset(g, 0, sizeof(*g));
	g->in = g->out = g->err = -1;

	if (!gpgsign_vars_ok())
		return -1;

	cmd = gpgsign_command(detached);
	makeargv(cmd, &argc, &argv);
	free(cmd);
	if (argc < 2) {
		freeargv(argc, argv);
		warn("GnuPG signing command is not set");
		return -1;
	}
	/* execvp needs a NULL sentinel, makeargv does not provide one */
	argv = xrealloc(argv, sizeof(char *) * (argc + 1));
	argv[argc] = NULL;

	if (pipe(inp) != 0) {
		freeargv(argc, argv);
		return -1;
	}
	if (pipe(outp) != 0) {
		close(inp[0]);
		close(inp[1]);
		freeargv(argc, argv);
		return -1;
	}
	if (pipe(errp) != 0) {
		close(inp[0]);
		close(inp[1]);
		close(outp[0]);
		close(outp[1]);
		freeargv(argc, argv);
		return -1;
	}

	tty = isatty(STDOUT_FILENO) ? ttyname(STDOUT_FILENO) : NULL;

	g->pid = fork();
	if (g->pid == -1) {
		close(inp[0]);
		close(inp[1]);
		close(outp[0]);
		close(outp[1]);
		close(errp[0]);
		close(errp[1]);
		freeargv(argc, argv);
		return -1;
	}
	if (g->pid == 0) {
		dup2(inp[0], STDIN_FILENO);
		dup2(outp[1], STDOUT_FILENO);
		dup2(errp[1], STDERR_FILENO);
		close(inp[0]);
		close(inp[1]);
		close(outp[0]);
		close(outp[1]);
		close(errp[0]);
		close(errp[1]);
		if (tty != NULL)
			setenv("GPG_TTY", tty, 1);
		execvp(argv[1], &argv[1]);
		_exit(127);
	}

	close(inp[0]);
	close(outp[1]);
	close(errp[1]);
	freeargv(argc, argv);

	g->in = inp[1];
	g->out = outp[0];
	g->err = errp[0];
	return 0;
}

int
gpgsign_feed(struct gpgsign *g, const char *data, size_t len)
{
	struct pollfd pfd;
	ssize_t       wr;

	while (len > 0) {
		gpgsign_drain(g, 0);
		pfd.fd = g->in;
		pfd.events = POLLOUT;
		if (poll(&pfd, 1, -1) == -1) {
			if (errno == EINTR)
				continue;
			return -1;
		}
		if (pfd.revents & (POLLERR | POLLHUP))
			return -1;
		wr = write(g->in, data, len);
		if (wr < 0) {
			if (errno == EINTR || errno == EAGAIN)
				continue;
			return -1;
		}
		data += wr;
		len -= (size_t)wr;
	}
	return 0;
}

int
gpgsign_finish(struct gpgsign *g, char **out, size_t *out_len)
{
	int status;

	*out = NULL;
	*out_len = 0;

	if (g->in != -1) {
		close(g->in);
		g->in = -1;
	}
	while (g->out != -1 || g->err != -1)
		gpgsign_drain(g, -1);

	status = -1;
	while (waitpid(g->pid, &status, 0) == -1 && errno == EINTR)
		;

	if (status != 0 || g->olen == 0) {
		if (g->ebuf != NULL)
			fwrite(g->ebuf, 1, g->elen, stderr);
		warn("GnuPG signing failed");
		free(g->obuf);
		free(g->ebuf);
		return -1;
	}

	free(g->ebuf);
	*out = g->obuf;
	*out_len = g->olen;
	return 0;
}

void
gpgsign_abort(struct gpgsign *g)
{
	if (g->in != -1)
		close(g->in);
	if (g->out != -1)
		close(g->out);
	if (g->err != -1)
		close(g->err);
	if (g->pid > 0)
		while (waitpid(g->pid, NULL, 0) == -1 && errno == EINTR)
			;
	free(g->obuf);
	free(g->ebuf);
}

int
gpgsign_buf(const char *data, size_t len, bool detached,
		char **out, size_t *out_len)
{
	struct gpgsign g;

	if (gpgsign_start(detached, &g) != 0)
		return -1;
	if (gpgsign_feed(&g, data, len) != 0) {
		gpgsign_abort(&g);
		warn("GnuPG signing failed");
		return -1;
	}
	return gpgsign_finish(&g, out, out_len);
}