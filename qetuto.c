/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.  	   - <antiq.hofer@gmail.com>
 *
 * qetuto: a C reimplementation of app-portage/getuto (getuto 1.18),
 * maintaining ${ROOT}/etc/portage/gnupg so the Gentoo release keys are
 * trusted for binary-package signatures.  Same behaviour, no bash, no
 * dependency on getuto being installed, it still drives gpg/gpgconf.
 */

#include "main.h"
#include "applets.h"

#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <xalloc.h>

#include "array.h"
#include "eat_file.h"
#include "rmspace.h"
#include "set.h"
#include "xasprintf.h"
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

static bool qet_quiet = true;
static char qet_home[_Q_PATH_MAX];
static char *qet_root;

/* NULL-terminated, built from QETUTO_KEYSERVERS / QETUTO_KEYS or the
 * Gentoo defaults; keyfiles are ROOT-prefixed absolute paths */
static char **qet_keyservers;
static char **qet_keyfiles;

/* split a whitespace/comma separated config value into a NULL-terminated
 * argv of xstrdup'd tokens */
static char **
qet_split_list(const char *s)
{
	array  *a   = array_new();
	char   *buf = xstrdup(s);
	char   *tok;
	char   *sp;
	char  **out;
	size_t  i;
	char   *e;

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

static void
qet_build_lists(void)
{
	if (qetuto_keyservers_conf != NULL && qetuto_keyservers_conf[0] != '\0') {
		qet_keyservers = qet_split_list(qetuto_keyservers_conf);
	} else {
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
		const char *spec = (qetuto_keys_conf != NULL &&
							qetuto_keys_conf[0] != '\0')
				? qetuto_keys_conf : QET_KEYS_DEFAULT;
		char  **rel = qet_split_list(spec);
		size_t  n   = 0;
		size_t  i;

		while (rel[n] != NULL)
			n++;
		qet_keyfiles = xmalloc(sizeof(*qet_keyfiles) * (n + 1));
		for (i = 0; i < n; i++) {
			char p[_Q_PATH_MAX];

			snprintf(p, sizeof(p), "%s%s%s", qet_root,
					 rel[i][0] == '/' ? "" : "/", rel[i]);
			qet_keyfiles[i] = xstrdup(p);
			free(rel[i]);
		}
		qet_keyfiles[n] = NULL;
		free(rel);
	}
}

static void
qet_free_lists(void)
{
	size_t i;

	if (qet_keyservers != NULL) {
		for (i = 0; qet_keyservers[i] != NULL; i++)
			free(qet_keyservers[i]);
		free(qet_keyservers);
		qet_keyservers = NULL;
	}
	if (qet_keyfiles != NULL) {
		for (i = 0; qet_keyfiles[i] != NULL; i++)
			free(qet_keyfiles[i]);
		free(qet_keyfiles);
		qet_keyfiles = NULL;
	}
}

/* fork/exec argv; optional stdin feed, optional stdout capture (malloc'd
 * into *out).  Returns the child exit status, or -1 on spawn failure. */
static int
qet_spawn(char *const argv[], const char *input, char **out)
{
	int   inpipe[2]  = { -1, -1 };
	int   outpipe[2] = { -1, -1 };
	pid_t pid;
	int   status;

	if (input != NULL && pipe(inpipe) != 0)
		return -1;
	if (out != NULL && pipe(outpipe) != 0) {
		if (input != NULL) {
			close(inpipe[0]);
			close(inpipe[1]);
		}
		return -1;
	}

	pid = fork();
	if (pid < 0) {
		if (input != NULL) {
			close(inpipe[0]);
			close(inpipe[1]);
		}
		if (out != NULL) {
			close(outpipe[0]);
			close(outpipe[1]);
		}
		return -1;
	}
	if (pid == 0) {
		if (input != NULL) {
			dup2(inpipe[0], STDIN_FILENO);
			close(inpipe[0]);
			close(inpipe[1]);
		}
		if (out != NULL) {
			dup2(outpipe[1], STDOUT_FILENO);
			close(outpipe[0]);
			close(outpipe[1]);
		}
		execvp(argv[0], argv);
		_exit(127);
	}

	if (input != NULL) {
		close(inpipe[0]);
		/* child may have died; it is reaped below regardless */
		if (write(inpipe[1], input, strlen(input)) < 0)
			(void)0;
		close(inpipe[1]);
	}
	if (out != NULL) {
		size_t cap = 4096;
		size_t len = 0;
		char  *buf = xmalloc(cap);
		ssize_t n;

		close(outpipe[1]);
		while ((n = read(outpipe[0], buf + len, cap - len - 1)) > 0) {
			len += (size_t)n;
			if (len + 1 >= cap) {
				cap *= 2;
				buf = xrealloc(buf, cap);
			}
		}
		close(outpipe[0]);
		buf[len] = '\0';
		*out = buf;
	}

	if (waitpid(pid, &status, 0) < 0)
		return -1;
	return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

/* assemble a gpg argv: "gpg" [--quiet --no-permission-warning] extra...
 * extra is a NULL-terminated list; result is NULL-terminated */
static void
qet_gpg_argv(char **av, size_t avlen, const char *first, ...)
{
	va_list ap;
	size_t  n = 0;
	const char *a;

	av[n++] = (char *)"gpg";
	if (qet_quiet) {
		av[n++] = (char *)"--quiet";
		av[n++] = (char *)"--no-permission-warning";
	}
	if (first != NULL) {
		av[n++] = (char *)first;
		va_start(ap, first);
		while ((a = va_arg(ap, const char *)) != NULL && n < avlen - 1)
			av[n++] = (char *)a;
		va_end(ap);
	}
	av[n] = NULL;
}

/* split a gpg --with-colons line in place; empty fields preserved
 * (strtok collapses them, which corrupts fixed-position field access) */
static int
qet_colon_fields(char *line, char **fields, int maxf)
{
	int   nf = 0;
	char *p;

	fields[nf++] = line;
	for (p = line; *p != '\0' && nf < maxf; p++)
		if (*p == ':') {
			*p = '\0';
			fields[nf++] = p + 1;
		}
	return nf;
}

static void
qet_gpgconf_kill(void)
{
	char *av[] = { (char *)"gpgconf", (char *)"--kill", (char *)"all",
				   NULL };

	(void)qet_spawn(av, NULL, NULL);
}

/* the WKD refresh: locate every imported key's UID email via WKD */
static void
qet_wkd_locate(void)
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
	if (qet_spawn(av, NULL, &keys) != 0 || keys == NULL) {
		free(keys);
		return;
	}

	emails = create_set();
	for (line = strtok_r(keys, "\n", &sp);
		 line != NULL;
		 line = strtok_r(NULL, "\n", &sp))
	{
		char  *fields[16];
		int    nf;
		char  *lt, *gt, *at;

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
		at = strchr(lt + 1, '@');
		if (at == NULL || strchr(at + 1, '.') == NULL)
			continue;
		add_set(lt + 1, emails);
	}
	free(keys);

	ekeys = set_keys(emails);
	nloc = array_cnt(ekeys);
	if (nloc == 0) {
		array_free(ekeys);
		free_set(emails);
		return;
	}

	loc = xmalloc(sizeof(*loc) * (nloc + 6));
	nloc = 0;
	loc[nloc++] = (char *)"gpg";
	if (qet_quiet) {
		loc[nloc++] = (char *)"--quiet";
		loc[nloc++] = (char *)"--no-permission-warning";
	}
	loc[nloc++] = (char *)"--auto-key-locate=clear,nodefault,wkd";
	loc[nloc++] = (char *)"--locate-key";
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
static set *
qet_fingerprints(bool secret, const char *exclude)
{
	char  *av[8];
	char  *out = NULL;
	char  *line;
	char  *sp;
	set   *fps = create_set();

	qet_gpg_argv(av, 8, "--batch",
				 secret ? "--list-secret-keys" : "--list-keys",
				 "--keyid-format=long", "--with-colons", NULL);
	if (qet_spawn(av, NULL, &out) != 0 || out == NULL) {
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
		if (nf < 10 || fields[9][0] == '\0')
			continue;
		if (exclude != NULL && strcmp(fields[9], exclude) == 0)
			continue;
		add_set(fields[9], fps);
	}
	free(out);
	return fps;
}

static int
qet_refresh(const char *lastrun)
{
	struct stat st;
	time_t      now = time(NULL);
	time_t      lst = 0;
	char       *av[16];
	size_t      k;

	if (stat(lastrun, &st) == 0)
		lst = st.st_mtime;
	if (now - 86400 < lst) {
		if (!qet_quiet)
			printf("GnuPG keyring for package signatures already "
				   "up-to-date.\n");
		return 0;
	}
	if (!qet_quiet)
		printf("Updating GnuPG keyring for package signatures\n");

	for (k = 0; qet_keyfiles[k] != NULL; k++) {
		qet_gpg_argv(av, 16, "--batch", "--import", qet_keyfiles[k], NULL);
		(void)qet_spawn(av, NULL, NULL);
	}

	for (k = 0; qet_keyservers[k] != NULL; k++) {
		char *tav[16];
		size_t n = 0;

		tav[n++] = (char *)"timeout";
		tav[n++] = (char *)"-k";
		tav[n++] = (char *)QET_GPG_KILL;
		tav[n++] = (char *)QET_GPG_TERM;
		tav[n++] = (char *)"gpg";
		if (qet_quiet) {
			tav[n++] = (char *)"--quiet";
			tav[n++] = (char *)"--no-permission-warning";
		}
		tav[n++] = (char *)"--batch";
		tav[n++] = (char *)"--keyserver";
		tav[n++] = (char *)qet_keyservers[k];
		tav[n++] = (char *)"--refresh-keys";
		tav[n] = NULL;
		(void)qet_spawn(tav, NULL, NULL);
	}

	qet_wkd_locate();
	{
		int fd = open(lastrun, O_WRONLY | O_CREAT, 0644);

		if (fd >= 0)
			close(fd);
	}
	return 0;
}

static int
qet_bootstrap(const char *lastrun)
{
	char   staging[_Q_PATH_MAX + 16];
	char   orig[_Q_PATH_MAX];
	char   path[_Q_PATH_MAX + 32];
	char  *rmav[4];
	char  *av[24];
	FILE  *f;
	char  *pass = NULL;
	char  *mykeyid = NULL;
	set   *relkeys;
	array *relarr;
	size_t i;
	char  *fp;
	struct stat st;

	snprintf(orig, sizeof(orig), "%s", qet_home);
	snprintf(staging, sizeof(staging), "%s.getuto.tmp", qet_home);

	rmav[0] = (char *)"rm";
	rmav[1] = (char *)"-rf";
	rmav[2] = staging;
	rmav[3] = NULL;
	(void)qet_spawn(rmav, NULL, NULL);

	if (mkdir_p(staging, 0755) != 0) {
		warnp("cannot create %s", staging);
		return 1;
	}
	chmod(staging, 0755);
	setenv("GNUPGHOME", staging, 1);

	snprintf(path, sizeof(path), "%s/dirmngr.conf", staging);
	f = fopen(path, "w");
	if (f != NULL) {
		fputs("honor-http-proxy\nno-use-tor\nstandard-resolver\n"
			  "resolver-timeout 90\nconnect-timeout 90\n", f);
		fclose(f);
	}
	snprintf(path, sizeof(path), "%s/gpg-agent.conf", staging);
	f = fopen(path, "w");
	if (f != NULL) {
		fputs("disable-scdaemon\n", f);
		fclose(f);
	}
	snprintf(path, sizeof(path), "%s/gpg.conf", staging);
	f = fopen(path, "w");
	if (f != NULL) {
		fputs("no-greeting\n", f);
		fclose(f);
	}

	{
		char *oav[] = { (char *)"openssl", (char *)"rand",
						(char *)"-base64", (char *)"32", NULL };

		if (qet_spawn(oav, NULL, &pass) != 0 || pass == NULL) {
			warn("could not generate a passphrase (openssl)");
			goto fail;
		}
		rmspace(pass);
	}

	{
		char  keycfg[_Q_PATH_MAX + 48];
		char *cfgbuf;
		int   fd;

		snprintf(keycfg, sizeof(keycfg), "%s/.keycfg.XXXXXX", staging);
		fd = mkstemp(keycfg);
		if (fd < 0) {
			warnp("mkstemp failed");
			goto fail;
		}
		fchmod(fd, 0600);
		xasprintf(&cfgbuf,
			"%%echo Generating Portage local OpenPGP trust key\n"
			"Key-Type: RSA\nKey-Length: 3072\n"
			"Subkey-Type: RSA\nSubkey-Length: 3072\n"
			"Name-Real: Portage Local Trust Key\n"
			"Name-Comment: local signing only\n"
			"Name-Email: portage@localhost\n"
			"Expire-Date: 0\nPassphrase: %s\n%%commit\n%%echo done\n",
			pass);
		if (write(fd, cfgbuf, strlen(cfgbuf)) < 0)
			warnp("writing key config");
		close(fd);
		free(cfgbuf);

		qet_gpg_argv(av, 24, "--batch", "--generate-key", keycfg, NULL);
		if (qet_spawn(av, NULL, NULL) != 0) {
			unlink(keycfg);
			warn("gpg --generate-key failed");
			goto fail;
		}
		unlink(keycfg);
	}

	snprintf(path, sizeof(path), "%s/pass", staging);
	f = fopen(path, "w");
	if (f == NULL) {
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
	if (mykeyid == NULL) {
		warn("could not determine local trust key fingerprint");
		goto fail;
	}
	snprintf(path, sizeof(path), "%s/mykeyid", staging);
	f = fopen(path, "w");
	if (f != NULL) {
		fprintf(f, "%s\n", mykeyid);
		fclose(f);
	}

	{
		size_t kf;
		int    imported = 0;

		for (kf = 0; qet_keyfiles[kf] != NULL; kf++) {
			if (stat(qet_keyfiles[kf], &st) != 0)
				continue;
			qet_gpg_argv(av, 24, "--batch", "--import", qet_keyfiles[kf],
						 NULL);
			if (qet_spawn(av, NULL, NULL) == 0)
				imported++;
		}
		if (imported == 0) {
			warn("no release keyring found (checked %s). Is "
				 "sec-keys/openpgp-keys-gentoo-release installed?",
				 qet_keyfiles[0]);
			goto fail;
		}
	}

	relkeys = qet_fingerprints(false, mykeyid);
	relarr  = set_keys(relkeys);

	for (size_t k = 0; qet_keyservers[k] != NULL; k++) {
		char  *tav[64];
		size_t n = 0;

		tav[n++] = (char *)"timeout";
		tav[n++] = (char *)"-k";
		tav[n++] = (char *)QET_GPG_KILL;
		tav[n++] = (char *)QET_GPG_TERM;
		tav[n++] = (char *)"gpg";
		if (qet_quiet) {
			tav[n++] = (char *)"--quiet";
			tav[n++] = (char *)"--no-permission-warning";
		}
		tav[n++] = (char *)"--batch";
		tav[n++] = (char *)"--keyserver";
		tav[n++] = (char *)qet_keyservers[k];
		tav[n++] = (char *)"--recv-keys";
		array_for_each(relarr, i, fp)
			if (n < 62)
				tav[n++] = fp;
		tav[n] = NULL;
		(void)qet_spawn(tav, NULL, NULL);
	}

	qet_wkd_locate();

	{
		char passfile[_Q_PATH_MAX + 48];

		snprintf(passfile, sizeof(passfile), "%s/pass", staging);
		array_for_each(relarr, i, fp) {
			char *lav[16];
			size_t n = 0;

			lav[n++] = (char *)"gpg";
			if (qet_quiet) {
				lav[n++] = (char *)"--quiet";
				lav[n++] = (char *)"--no-permission-warning";
			}
			lav[n++] = (char *)"--batch";
			lav[n++] = (char *)"--yes";
			lav[n++] = (char *)"--no-tty";
			lav[n++] = (char *)"--passphrase-file";
			lav[n++] = passfile;
			lav[n++] = (char *)"--pinentry-mode";
			lav[n++] = (char *)"loopback";
			lav[n++] = (char *)"--quick-lsign-key";
			lav[n++] = fp;
			lav[n] = NULL;
			if (qet_spawn(lav, NULL, NULL) != 0) {
				char *fav[18];
				size_t m = 0;

				fav[m++] = (char *)"gpg";
				if (qet_quiet) {
					fav[m++] = (char *)"--quiet";
					fav[m++] = (char *)"--no-permission-warning";
				}
				fav[m++] = (char *)"--command-fd";
				fav[m++] = (char *)"0";
				fav[m++] = (char *)"--yes";
				fav[m++] = (char *)"--no-tty";
				fav[m++] = (char *)"--passphrase-file";
				fav[m++] = passfile;
				fav[m++] = (char *)"--pinentry-mode";
				fav[m++] = (char *)"loopback";
				fav[m++] = (char *)"--lsign-key";
				fav[m++] = fp;
				fav[m] = NULL;
				(void)qet_spawn(fav, "y\ny\n", NULL);
			}
		}
	}
	array_free(relarr);
	free_set(relkeys);

	qet_gpg_argv(av, 24, "--batch", "--check-trustdb", NULL);
	(void)qet_spawn(av, NULL, NULL);

	snprintf(path, sizeof(path), "%s/trustdb.gpg", staging);
	chmod(path, 0644);

	if (rename(staging, orig) != 0) {
		warnp("cannot move %s into place", staging);
		goto fail;
	}
	setenv("GNUPGHOME", orig, 1);

	{
		int fd = open(lastrun, O_WRONLY | O_CREAT, 0644);

		if (fd >= 0)
			close(fd);
	}

	free(pass);
	free(mykeyid);
	return 0;

 fail:
	free(pass);
	free(mykeyid);
	rmav[2] = staging;
	(void)qet_spawn(rmav, NULL, NULL);
	return 1;
}

int qetuto_main(int argc, char **argv)
{
	int         ret;
	char        lastrun[_Q_PATH_MAX + 16];
	char        trustdb[_Q_PATH_MAX + 16];
	size_t      rl;
	struct stat st;

	while ((ret = GETOPT_LONG(QETUTO, qetuto, "")) != -1) {
		switch (ret) {
			COMMON_GETOPTS_CASES(qetuto)
		}
	}

	qet_quiet = verbose == 0;

	if (geteuid() != 0)
		err("qetuto must be run as root");

	qet_root = xstrdup(portroot);
	rl = strlen(qet_root);
	while (rl > 1 && qet_root[rl - 1] == '/')
		qet_root[--rl] = '\0';
	if (strcmp(qet_root, "/") == 0)
		qet_root[0] = '\0';

	snprintf(qet_home, sizeof(qet_home), "%s/etc/portage/gnupg", qet_root);
	setenv("GNUPGHOME", qet_home, 1);
	snprintf(lastrun, sizeof(lastrun), "%s/.getuto.last", qet_home);

	qet_build_lists();

	qet_gpgconf_kill();

	if (stat(qet_home, &st) != 0) {
		if (!qet_quiet)
			printf("Initializing %s\n", qet_home);
		ret = qet_bootstrap(lastrun);
	} else {
		setenv("LC_ALL", "C.UTF-8", 1);
		ret = qet_refresh(lastrun);
	}

	snprintf(trustdb, sizeof(trustdb), "%s/trustdb.gpg", qet_home);
	chmod(trustdb, 0644);

	qet_gpgconf_kill();
	qet_free_lists();
	free(qet_root);
	qet_root = NULL;
	return ret;
}
