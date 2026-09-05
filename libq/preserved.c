/*
 * Copyright 2026-     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 * 
 * The official implementation of preservation of libraries, backup
 * and restoration.
 * Implementing a portage parity feature, that can be used in the future
 * for various other actions.
 */

#include "main.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <xalloc.h>

#include "xasprintf.h"

#include "atom.h"
#include "array.h"
#include "eat_file.h"
#include "preserved.h"

struct preserved_reg_ {
	char  *file;
	int    fd;
	array *entries;
	char  *orig;
	size_t origlen;
};

static char *
pres_strndup(const char *s, size_t len)
{
	char *ret = xmalloc(len + 1);

	memcpy(ret, s, len);
	ret[len] = '\0';
	return ret;
}

static void
pres_entry_free(void *e)
{
	preserved_entry *pe = e;

	if (pe == NULL)
		return;
	free(pe->cps);
	free(pe->cpv);
	free(pe->counter);
	array_deepfree(pe->paths, free);
	free(pe);
}

static char *
pres_counter_norm(const char *counter)
{
	const char *s = counter != NULL ? counter : "";
	size_t      len;

	while (*s != '\0' && isspace((unsigned char)*s))
		s++;
	len = strlen(s);
	while (len > 0 && isspace((unsigned char)s[len - 1]))
		len--;
	return pres_strndup(s, len);
}

struct pres_json {
	const char *p;
	const char *end;
	int         depth;
};

static void
pres_json_ws(struct pres_json *j)
{
	while (j->p < j->end &&
			(*j->p == ' ' || *j->p == '\t' ||
			 *j->p == '\n' || *j->p == '\r'))
		j->p++;
}

static bool pres_json_skip(struct pres_json *j);

static int
pres_json_hex(char c)
{
	if (c >= '0' && c <= '9')
		return c - '0';
	if (c >= 'a' && c <= 'f')
		return c - 'a' + 10;
	if (c >= 'A' && c <= 'F')
		return c - 'A' + 10;
	return -1;
}

static size_t
pres_json_utf8(unsigned long cp, char out[4])
{
	if (cp < 0x80) {
		out[0] = (char)cp;
		return 1;
	}
	if (cp < 0x800) {
		out[0] = (char)(0xC0 | (cp >> 6));
		out[1] = (char)(0x80 | (cp & 0x3F));
		return 2;
	}
	if (cp < 0x10000) {
		out[0] = (char)(0xE0 | (cp >> 12));
		out[1] = (char)(0x80 | ((cp >> 6) & 0x3F));
		out[2] = (char)(0x80 | (cp & 0x3F));
		return 3;
	}
	out[0] = (char)(0xF0 | (cp >> 18));
	out[1] = (char)(0x80 | ((cp >> 12) & 0x3F));
	out[2] = (char)(0x80 | ((cp >> 6) & 0x3F));
	out[3] = (char)(0x80 | (cp & 0x3F));
	return 4;
}

static char *
pres_json_string(struct pres_json *j)
{
	FILE   *m;
	char   *out  = NULL;
	size_t  olen = 0;

	pres_json_ws(j);
	if (j->p >= j->end || *j->p != '"')
		return NULL;
	j->p++;
	m = open_memstream(&out, &olen);
	if (m == NULL)
		return NULL;
	while (j->p < j->end && *j->p != '"') {
		unsigned char c = (unsigned char)*j->p;

		if (c == '\\') {
			j->p++;
			if (j->p >= j->end)
				break;
			switch (*j->p) {
			case '"':  fputc('"', m);  j->p++; break;
			case '\\': fputc('\\', m); j->p++; break;
			case '/':  fputc('/', m);  j->p++; break;
			case 'b':  fputc('\b', m); j->p++; break;
			case 'f':  fputc('\f', m); j->p++; break;
			case 'n':  fputc('\n', m); j->p++; break;
			case 'r':  fputc('\r', m); j->p++; break;
			case 't':  fputc('\t', m); j->p++; break;
			case 'u': {
				unsigned long cp = 0;
				char          u8[4];
				size_t        ul;
				int           k;
				int           h;

				j->p++;
				if (j->end - j->p < 4)
					goto sfail;
				for (k = 0; k < 4; k++) {
					h = pres_json_hex(j->p[k]);
					if (h < 0)
						goto sfail;
					cp = (cp << 4) | (unsigned)h;
				}
				j->p += 4;
				if (cp >= 0xD800 && cp <= 0xDBFF &&
						j->end - j->p >= 6 &&
						j->p[0] == '\\' && j->p[1] == 'u') {
					unsigned long lo = 0;

					for (k = 0; k < 4; k++) {
						h = pres_json_hex(j->p[2 + k]);
						if (h < 0)
							goto sfail;
						lo = (lo << 4) | (unsigned)h;
					}
					if (lo >= 0xDC00 && lo <= 0xDFFF) {
						cp = 0x10000 +
							((cp - 0xD800) << 10) + (lo - 0xDC00);
						j->p += 6;
					}
				}
				ul = pres_json_utf8(cp, u8);
				fwrite(u8, 1, ul, m);
				break;
			}
			default:
				goto sfail;
			}
		} else if (c < 0x20) {
			goto sfail;
		} else {
			fputc((int)c, m);
			j->p++;
		}
	}
	if (j->p >= j->end || *j->p != '"')
		goto sfail;
	j->p++;
	fclose(m);
	return out != NULL ? out : xstrdup("");

sfail:
	fclose(m);
	free(out);
	return NULL;
}

static char *
pres_json_scalar(struct pres_json *j)
{
	pres_json_ws(j);
	if (j->p < j->end && *j->p == '"')
		return pres_json_string(j);
	if (j->p < j->end &&
			(*j->p == '-' || (*j->p >= '0' && *j->p <= '9'))) {
		const char *s = j->p;

		if (*j->p == '-')
			j->p++;
		while (j->p < j->end &&
				((*j->p >= '0' && *j->p <= '9') ||
				 *j->p == '.' || *j->p == 'e' || *j->p == 'E' ||
				 *j->p == '+' || *j->p == '-'))
			j->p++;
		return pres_strndup(s, (size_t)(j->p - s));
	}
	return NULL;
}

static bool
pres_json_lit(struct pres_json *j, const char *lit)
{
	size_t l = strlen(lit);

	if ((size_t)(j->end - j->p) >= l &&
			memcmp(j->p, lit, l) == 0) {
		j->p += l;
		return true;
	}
	return false;
}

static bool
pres_json_skip(struct pres_json *j)
{
	pres_json_ws(j);
	if (j->p >= j->end || j->depth > 32)
		return false;
	if (*j->p == '"') {
		char *s = pres_json_string(j);

		if (s == NULL)
			return false;
		free(s);
		return true;
	}
	if (*j->p == '[' || *j->p == '{') {
		char open  = *j->p;
		char close = open == '[' ? ']' : '}';

		j->p++;
		j->depth++;
		pres_json_ws(j);
		if (j->p < j->end && *j->p == close) {
			j->p++;
			j->depth--;
			return true;
		}
		for (;;) {
			if (open == '{') {
				char *k = pres_json_string(j);

				if (k == NULL)
					return false;
				free(k);
				pres_json_ws(j);
				if (j->p >= j->end || *j->p != ':')
					return false;
				j->p++;
			}
			if (!pres_json_skip(j))
				return false;
			pres_json_ws(j);
			if (j->p >= j->end)
				return false;
			if (*j->p == ',') {
				j->p++;
				continue;
			}
			if (*j->p == close) {
				j->p++;
				j->depth--;
				return true;
			}
			return false;
		}
	}
	if (pres_json_lit(j, "true") || pres_json_lit(j, "false") ||
			pres_json_lit(j, "null"))
		return true;
	{
		char *n = pres_json_scalar(j);

		if (n == NULL)
			return false;
		free(n);
		return true;
	}
}

static preserved_entry *
pres_json_entry(struct pres_json *j, char *cps)
{
	preserved_entry *pe;
	char            *cpv     = NULL;
	char            *counter = NULL;
	array           *paths   = NULL;

	pres_json_ws(j);
	if (j->p >= j->end || *j->p != '[')
		goto efail;
	j->p++;
	cpv = pres_json_string(j);
	if (cpv == NULL)
		goto efail;
	pres_json_ws(j);
	if (j->p >= j->end || *j->p != ',')
		goto efail;
	j->p++;
	counter = pres_json_scalar(j);
	if (counter == NULL)
		goto efail;
	pres_json_ws(j);
	if (j->p >= j->end || *j->p != ',')
		goto efail;
	j->p++;
	pres_json_ws(j);
	if (j->p >= j->end || *j->p != '[')
		goto efail;
	j->p++;
	paths = array_new();
	pres_json_ws(j);
	if (j->p < j->end && *j->p == ']') {
		j->p++;
	} else {
		for (;;) {
			char *pt = pres_json_string(j);

			if (pt == NULL)
				goto efail;
			array_append(paths, pt);
			pres_json_ws(j);
			if (j->p < j->end && *j->p == ',') {
				j->p++;
				continue;
			}
			if (j->p < j->end && *j->p == ']') {
				j->p++;
				break;
			}
			goto efail;
		}
	}
	pres_json_ws(j);
	if (j->p >= j->end || *j->p != ']')
		goto efail;
	j->p++;

	pe = xzalloc(sizeof(*pe));
	pe->cps = cps;
	pe->cpv = cpv;
	pe->counter = pres_counter_norm(counter);
	free(counter);
	pe->paths = paths;
	return pe;

efail:
	free(cps);
	free(cpv);
	free(counter);
	if (paths != NULL)
		array_deepfree(paths, free);
	return NULL;
}

static void
pres_parse(preserved_reg *reg, const char *buf, size_t len)
{
	struct pres_json j;

	j.p     = buf;
	j.end   = buf + len;
	j.depth = 0;

	pres_json_ws(&j);
	if (j.p >= j.end || *j.p != '{')
		return;
	j.p++;
	pres_json_ws(&j);
	if (j.p < j.end && *j.p == '}')
		return;
	for (;;) {
		char            *key;
		preserved_entry *pe;

		key = pres_json_string(&j);
		if (key == NULL)
			return;
		pres_json_ws(&j);
		if (j.p >= j.end || *j.p != ':') {
			free(key);
			return;
		}
		j.p++;
		pe = pres_json_entry(&j, key);
		if (pe != NULL) {
			array_append(reg->entries, pe);
		} else {
			if (!pres_json_skip(&j))
				return;
		}
		pres_json_ws(&j);
		if (j.p >= j.end)
			return;
		if (*j.p == ',') {
			j.p++;
			continue;
		}
		return;
	}
}

static preserved_reg *
pres_open(const char *file, bool writable)
{
	preserved_reg *reg;
	struct flock   fl;
	char          *buf  = NULL;
	size_t         blen = 0;

	reg = xzalloc(sizeof(*reg));
	reg->file    = xstrdup(file);
	reg->entries = array_new();
	reg->fd      = -1;
	if (writable)
		reg->fd = open(file, O_RDWR | O_CREAT | O_CLOEXEC, 0644);
	if (reg->fd < 0)
		reg->fd = open(file, O_RDONLY | O_CLOEXEC);
	if (reg->fd >= 0 && writable) {
		int fdfl = fcntl(reg->fd, F_GETFL);

		memset(&fl, 0, sizeof(fl));
		fl.l_type   = (fdfl != -1 && (fdfl & O_ACCMODE) == O_RDONLY)
				? F_RDLCK : F_WRLCK;
		fl.l_whence = SEEK_SET;
		if (fcntl(reg->fd, F_SETLK, &fl) != 0) {
			if (errno == EACCES || errno == EAGAIN)
				warn("waiting for preserved-libs registry lock %s", file);
			while (fcntl(reg->fd, F_SETLKW, &fl) != 0) {
				if (errno != EINTR)
					break;
			}
		}
	}
	if (reg->fd >= 0) {
		if (eat_file_fd(reg->fd, &buf, &blen) && buf != NULL) {
			reg->origlen = strlen(buf);
			reg->orig    = buf;
			pres_parse(reg, reg->orig, reg->origlen);
			buf = NULL;
		}
	}
	if (buf != NULL)
		free(buf);
	if (reg->orig == NULL) {
		reg->orig    = xstrdup("");
		reg->origlen = 0;
	}
	return reg;
}

preserved_reg *
preserved_open(const char *file)
{
	return pres_open(file, true);
}

preserved_reg *
preserved_open_ro(const char *file)
{
	return pres_open(file, false);
}

static preserved_entry *
pres_find(preserved_reg *reg, const char *cps, size_t *idx)
{
	size_t           i;
	preserved_entry *pe;

	array_for_each(reg->entries, i, pe) {
		if (strcmp(pe->cps, cps) == 0) {
			if (idx != NULL)
				*idx = i;
			return pe;
		}
	}
	return NULL;
}

static char *
pres_cps(const char *cpv, const char *slot)
{
	atom_ctx *a = atom_explode(cpv);
	char     *ret;

	if (a == NULL || a->CATEGORY == NULL || a->PN == NULL) {
		if (a != NULL)
			atom_implode(a);
		xasprintf(&ret, "%s:%s", cpv, slot != NULL ? slot : "0");
		return ret;
	}
	xasprintf(&ret, "%s/%s:%s", a->CATEGORY, a->PN,
			  slot != NULL ? slot : "0");
	atom_implode(a);
	return ret;
}

static int
pres_strp_cmp(const void *l, const void *r)
{
	return strcmp(*(char * const *)l, *(char * const *)r);
}

void
preserved_register(preserved_reg *reg, const char *cpv, const char *slot,
				   const char *counter, array *paths)
{
	char            *cps  = pres_cps(cpv, slot);
	char            *ncnt = pres_counter_norm(counter);
	size_t           idx  = 0;
	preserved_entry *pe   = pres_find(reg, cps, &idx);
	size_t           i;
	char            *pt;

	if ((paths == NULL || array_cnt(paths) == 0) && pe != NULL &&
			strcmp(pe->cpv, cpv) == 0 &&
			strcmp(pe->counter, ncnt) == 0) {
		array_delete(reg->entries, idx, pres_entry_free);
	} else if (paths != NULL && array_cnt(paths) > 0) {
		if (pe != NULL)
			array_delete(reg->entries, idx, pres_entry_free);
		pe = xzalloc(sizeof(*pe));
		pe->cps     = xstrdup(cps);
		pe->cpv     = xstrdup(cpv);
		pe->counter = xstrdup(ncnt);
		pe->paths   = array_new();
		array_for_each(paths, i, pt)
			array_append(pe->paths, xstrdup(pt));
		array_sort(pe->paths, pres_strp_cmp);
		array_append(reg->entries, pe);
	}
	free(cps);
	free(ncnt);
}

void
preserved_unregister(preserved_reg *reg, const char *cpv, const char *slot,
					 const char *counter)
{
	preserved_register(reg, cpv, slot, counter, NULL);
}

array *
preserved_entries(preserved_reg *reg)
{
	return reg->entries;
}

size_t
preserved_count(preserved_reg *reg)
{
	return array_cnt(reg->entries);
}

static char *
pres_norm(const char *dir, const char *target)
{
	char   *joined;
	char   *seg;
	char   *sp;
	array  *segs = array_new();
	size_t  i;
	FILE   *m;
	size_t  olen = 0;
	char   *obuf = NULL;

	if (target[0] == '/')
		joined = xstrdup(target);
	else
		xasprintf(&joined, "%s/%s", dir, target);

	for (seg = strtok_r(joined, "/", &sp);
		 seg != NULL;
		 seg = strtok_r(NULL, "/", &sp)) {
		if (strcmp(seg, ".") == 0)
			continue;
		if (strcmp(seg, "..") == 0) {
			if (array_cnt(segs) > 0)
				array_remove(segs, array_cnt(segs) - 1);
			continue;
		}
		array_append(segs, seg);
	}
	m = open_memstream(&obuf, &olen);
	if (m == NULL) {
		free(joined);
		array_free(segs);
		return xstrdup(target);
	}
	if (array_cnt(segs) == 0)
		fputc('/', m);
	array_for_each(segs, i, seg)
		fprintf(m, "/%s", seg);
	fclose(m);
	free(joined);
	array_free(segs);
	return obuf;
}

void
preserved_prune(preserved_reg *reg, const char *root)
{
	size_t i = 0;

	while (i < array_cnt(reg->entries)) {
		preserved_entry *pe    = array_get(reg->entries, i);
		array           *keep  = array_new();
		array           *hard  = array_new();
		array           *slnk  = array_new();
		array           *starg = array_new();
		size_t           n;
		char            *pt;
		struct stat      st;

		array_for_each(pe->paths, n, pt) {
			char *abs;

			xasprintf(&abs, "%s/%s",
					  root != NULL ? root : "",
					  pt[0] == '/' ? pt + 1 : pt);
			if (lstat(abs, &st) != 0) {
				free(abs);
				continue;
			}
			if (S_ISLNK(st.st_mode)) {
				char tbuf[8192];
				ssize_t tl = readlink(abs, tbuf, sizeof(tbuf) - 1);

				if (tl > 0) {
					tbuf[tl] = '\0';
					array_append(slnk, pt);
					array_append(starg, xstrdup(tbuf));
				}
			} else if (S_ISREG(st.st_mode)) {
				array_append(hard, pt);
				array_append(keep, xstrdup(pt));
			}
			free(abs);
		}

		array_for_each(slnk, n, pt) {
			char  *dir = xstrdup(pt);
			char  *sl  = strrchr(dir, '/');
			char  *resolved;
			size_t h;
			char  *hp;

			if (sl != NULL)
				*sl = '\0';
			else
				dir[0] = '\0';
			resolved = pres_norm(dir, array_get(starg, n));
			array_for_each(hard, h, hp) {
				if (strcmp(hp, resolved) == 0) {
					array_append(keep, xstrdup(pt));
					break;
				}
			}
			free(resolved);
			free(dir);
		}
		array_deepfree(starg, free);
		array_free(slnk);
		array_free(hard);

		if (array_cnt(keep) > 0) {
			array_deepfree(pe->paths, free);
			array_sort(keep, pres_strp_cmp);
			pe->paths = keep;
			i++;
		} else {
			array_free(keep);
			array_delete(reg->entries, i, pres_entry_free);
		}
	}
}

static void
pres_json_emit_str(FILE *f, const char *s)
{
	fputc('"', f);
	for (; *s != '\0'; s++) {
		unsigned char c = (unsigned char)*s;

		switch (c) {
		case '"':  fputs("\\\"", f); break;
		case '\\': fputs("\\\\", f); break;
		case '\n': fputs("\\n", f);  break;
		case '\t': fputs("\\t", f);  break;
		case '\r': fputs("\\r", f);  break;
		case '\b': fputs("\\b", f);  break;
		case '\f': fputs("\\f", f);  break;
		default:
			if (c < 0x20)
				fprintf(f, "\\u%04x", c);
			else
				fputc((int)c, f);
		}
	}
	fputc('"', f);
}

static int
pres_entry_cmp(const void *l, const void *r)
{
	const preserved_entry *le = *(preserved_entry * const *)l;
	const preserved_entry *re = *(preserved_entry * const *)r;

	return strcmp(le->cps, re->cps);
}

static char *
pres_serialize(preserved_reg *reg, size_t *lenp)
{
	FILE            *m;
	char            *out  = NULL;
	size_t           olen = 0;
	size_t           i;
	size_t           n;
	preserved_entry *pe;
	char            *pt;

	m = open_memstream(&out, &olen);
	if (m == NULL)
		return NULL;
	if (array_cnt(reg->entries) == 0) {
		fputs("{}", m);
	} else {
		array_sort(reg->entries, pres_entry_cmp);
		fputs("{\n", m);
		array_for_each(reg->entries, i, pe) {
			fputc('\t', m);
			pres_json_emit_str(m, pe->cps);
			fputs(": [\n\t\t", m);
			pres_json_emit_str(m, pe->cpv);
			fputs(",\n\t\t", m);
			pres_json_emit_str(m, pe->counter);
			fputs(",\n\t\t", m);
			if (array_cnt(pe->paths) == 0) {
				fputs("[]", m);
			} else {
				fputs("[\n", m);
				array_for_each(pe->paths, n, pt) {
					fputs("\t\t\t", m);
					pres_json_emit_str(m, pt);
					if (n + 1 < array_cnt(pe->paths))
						fputc(',', m);
					fputc('\n', m);
				}
				fputs("\t\t]", m);
			}
			fputs("\n\t]", m);
			if (i + 1 < array_cnt(reg->entries))
				fputc(',', m);
			fputc('\n', m);
		}
		fputc('}', m);
	}
	fclose(m);
	if (lenp != NULL)
		*lenp = olen;
	return out;
}

bool
preserved_store(preserved_reg *reg)
{
	char   *ser;
	size_t  slen = 0;
	char   *tmp;
	int     tfd;
	bool    ok   = false;
	const char *sb = getenv("SANDBOX_ON");

	if (sb != NULL && strcmp(sb, "1") == 0)
		return true;
	ser = pres_serialize(reg, &slen);
	if (ser == NULL)
		return false;
	if (slen == reg->origlen && memcmp(ser, reg->orig, slen) == 0) {
		free(ser);
		return true;
	}
	xasprintf(&tmp, "%s.XXXXXX", reg->file);
	tfd = mkstemp(tmp);
	if (tfd >= 0) {
		ssize_t wr = write(tfd, ser, slen);

		if (wr >= 0 && (size_t)wr == slen &&
				fchmod(tfd, 0644) == 0 &&
				close(tfd) == 0 &&
				rename(tmp, reg->file) == 0) {
			ok = true;
			free(reg->orig);
			reg->orig    = ser;
			reg->origlen = slen;
			ser = NULL;
		} else {
			if (tfd >= 0)
				close(tfd);
			unlink(tmp);
		}
	}
	free(tmp);
	free(ser);
	return ok;
}

void
preserved_close(preserved_reg *reg)
{
	if (reg == NULL)
		return;
	if (reg->fd >= 0)
		close(reg->fd);
	array_deepfree(reg->entries, pres_entry_free);
	free(reg->orig);
	free(reg->file);
	free(reg);
}