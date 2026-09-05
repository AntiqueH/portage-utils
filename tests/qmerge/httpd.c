/*
 * Copyright 2026-     Jaeger H.  - <antiq.hofer@gmail.com>
 * Distributed under the terms of the GNU General Public License v2
 *
 * our tiny static-GET http server for the qmerge test suite.
 * serves one directory on 127.0.0.1, prints "PORT <n>" once bound (port 0 =
 * whatever temporary), takes only one request per connection, HTTP/1.0, and GET only.
 * we're just mimicking a download, that's about it.
 */

#define _POSIX_C_SOURCE 200809L

#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <unistd.h>

int
main(int argc, char **argv)
{
	const char        *root = NULL;
	int                port = 0;
	int                srv;
	int                one  = 1;
	struct sockaddr_in sa;
	socklen_t          sl   = sizeof(sa);
	int                i;

	for (i = 1; i < argc - 1; i++) {
		if (strcmp(argv[i], "-p") == 0)
			port = atoi(argv[++i]);
		else if (strcmp(argv[i], "-d") == 0)
			root = argv[++i];
	}
	if (root == NULL) {
		fprintf(stderr, "usage: %s -d DIR [-p PORT]\n", argv[0]);
		return 1;
	}

	signal(SIGPIPE, SIG_IGN);

	srv = socket(AF_INET, SOCK_STREAM, 0);
	if (srv < 0)
		return 1;
	setsockopt(srv, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
	memset(&sa, 0, sizeof(sa));
	sa.sin_family = AF_INET;
	sa.sin_port   = htons((unsigned short)port);
	sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (bind(srv, (struct sockaddr *)&sa, sizeof(sa)) != 0 ||
			listen(srv, 16) != 0)
		return 1;
	if (getsockname(srv, (struct sockaddr *)&sa, &sl) != 0)
		return 1;
	printf("PORT %d\n", (int)ntohs(sa.sin_port));
	fflush(stdout);

	while (1) {
		int         c = accept(srv, NULL, NULL);
		char        req[4096];
		size_t      got = 0;
		ssize_t     n;
		char       *sp;
		char       *path;
		char        full[8192];
		int         fd;
		struct stat st;

		if (c < 0)
			continue;
		while (got < sizeof(req) - 1) {
			n = read(c, req + got, sizeof(req) - 1 - got);
			if (n <= 0)
				break;
			got += (size_t)n;
			req[got] = '\0';
			if (strstr(req, "\r\n\r\n") != NULL ||
					strstr(req, "\n\n") != NULL)
				break;
		}
		req[got] = '\0';

		fd = -1;
		if (strncmp(req, "GET /", 5) == 0) {
			path = req + 4;
			sp = strchr(path, ' ');
			if (sp != NULL)
				*sp = '\0';
			sp = strchr(path, '?');
			if (sp != NULL)
				*sp = '\0';
			if (strstr(path, "..") == NULL && path[1] != '\0') {
				snprintf(full, sizeof(full), "%s%s", root, path);
				fd = open(full, O_RDONLY);
				if (fd >= 0 && (fstat(fd, &st) != 0 ||
						!S_ISREG(st.st_mode))) {
					close(fd);
					fd = -1;
				}
			}
		}

		if (fd >= 0) {
			dprintf(c, "HTTP/1.0 200 OK\r\n"
					"Content-Length: %lld\r\n"
					"Content-Type: application/octet-stream\r\n"
					"Connection: close\r\n\r\n",
					(long long)st.st_size);
			while ((n = read(fd, full, sizeof(full))) > 0)
				if (write(c, full, (size_t)n) != n)
					break;
			close(fd);
		} else {
			dprintf(c, "HTTP/1.0 404 Not Found\r\n"
					"Content-Length: 9\r\n"
					"Connection: close\r\n\r\nnot found");
		}
		close(c);
	}
}