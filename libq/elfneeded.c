/*
 * Copyright -2026     Gentoo Authors
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>
 *
 * Minimal ELF dynamic-section reader. Both classes, both byte orders.
 * The arch tag is portage's multilib category (bug #534206) 
 * so it compares against the sixth field of VDB NEEDED.ELF.2 lines.
 * 
 * PS: funny enough, this our usual 'area of expertise' 
 */

#include "main.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <xalloc.h>

#include "eat_file.h"
#include "elfneeded.h"
#include "xasprintf.h"

static const struct {
	unsigned int  em;
	const char   *prefix;
} elf_needed_machines[] = {
	{      2, "sparc"  },
	{      3, "x86"    },
	{      4, "m68k"   },
	{      8, "mips"   },
	{     15, "hppa"   },
	{     18, "sparc"  },
	{     20, "ppc"    },
	{     21, "ppc"    },
	{     22, "s390"   },
	{     40, "arm"    },
	{     42, "sh"     },
	{     43, "sparc"  },
	{     45, "arc"    },
	{     50, "ia64"   },
	{     62, "x86"    },
	{     93, "arc"    },
	{    113, "nios2"  },
	{    175, "e2k"    },
	{    183, "arm"    },
	{    195, "arc"    },
	{    224, "amdgpu" },
	{    243, "riscv"  },
	{    247, "bpf"    },
	{    253, "arc"    },
	{    255, "arc"    },
	{    258, "loong"  },
	{ 0x9026, "alpha"  },
};

static const char *
elf_needed_suffix(unsigned int em, const char *prefix,
				  bool is64, uint32_t flags)
{
	if (strcmp(prefix, "loong") == 0) {
		switch (flags & 0x07) {
		case 0x1: return "lp64s";
		case 0x2: return "lp64f";
		case 0x3: return "lp64d";
		case 0x5: return "ilp32s";
		case 0x6: return "ilp32f";
		case 0x7: return "ilp32d";
		default:  return NULL;
		}
	}
	if (strcmp(prefix, "mips") == 0) {
		switch (flags & 0x0000F000) {
		case 0x1000: return "o32";
		case 0x2000: return "o64";
		case 0x3000: return "eabi32";
		case 0x4000: return "eabi64";
		case 0x0000: break;
		default:     return NULL;
		}
		if (flags & 0x20)
			return "n32";
		if (is64)
			return "n64";
		return NULL;
	}
	if (strcmp(prefix, "riscv") == 0) {
		if (flags == 0x1)
			return is64 ? "lp64" : "ilp32";
		if (flags == (0x1 | 0x4))
			return is64 ? "lp64d" : "ilp32d";
		return NULL;
	}
	if (is64)
		return "64";
	if (em == 62)
		return "x32";
	return "32";
}

static uint64_t
elf_needed_get(const unsigned char *p, size_t sz, bool msb)
{
	uint64_t v = 0;
	size_t   i;

	for (i = 0; i < sz; i++)
		v |= (uint64_t)p[msb ? i : sz - 1 - i] << (8 * (sz - 1 - i));
	return v;
}

static const char *
elf_needed_str(const char *buf, size_t len, size_t off)
{
	if (off >= len)
		return NULL;
	if (memchr(buf + off, '\0', len - off) == NULL)
		return NULL;
	return buf + off;
}

elf_needed *
elf_needed_read(const char *path)
{
	elf_needed          *en   = NULL;
	char                *buf  = NULL;
	size_t               len  = 0;
	const unsigned char *d;
	bool                 is64;
	bool                 msb;
	unsigned int         em;
	uint32_t             flags;
	uint64_t             phoff;
	uint64_t             phentsize;
	uint64_t             phnum;
	uint64_t             dynoff   = 0;
	uint64_t             dynsz    = 0;
	uint64_t             strvaddr = 0;
	uint64_t             stroff   = 0;
	uint64_t             sonoff   = 0;
	bool                 hasson   = false;
	array               *needoffs = NULL;
	size_t               i;
	size_t               esz;

	if (!eat_file(path, &buf, &len) || buf == NULL || len < 52)
		goto out;
	d = (const unsigned char *)buf;
	if (memcmp(d, "\177ELF", 4) != 0)
		goto out;
	if (d[4] != 1 && d[4] != 2)
		goto out;
	if (d[5] != 1 && d[5] != 2)
		goto out;
	is64 = d[4] == 2;
	msb  = d[5] == 2;
	if (is64 && len < 64)
		goto out;

	em        = (unsigned int)elf_needed_get(d + 18, 2, msb);
	flags     = (uint32_t)elf_needed_get(d + (is64 ? 48 : 36), 4, msb);
	phoff     = elf_needed_get(d + (is64 ? 32 : 28), is64 ? 8 : 4, msb);
	phentsize = elf_needed_get(d + (is64 ? 54 : 42), 2, msb);
	phnum     = elf_needed_get(d + (is64 ? 56 : 44), 2, msb);
	if (phentsize < (uint64_t)(is64 ? 56 : 32) || phnum > 2048)
		goto out;

	for (i = 0; i < phnum; i++) {
		uint64_t po = phoff + (uint64_t)i * phentsize;

		if (po > len || phentsize > len - po)
			goto out;
		if (elf_needed_get(d + po, 4, msb) == 2) {
			dynoff = elf_needed_get(d + po + (is64 ?  8 :  4),
									is64 ? 8 : 4, msb);
			dynsz  = elf_needed_get(d + po + (is64 ? 32 : 16),
									is64 ? 8 : 4, msb);
			break;
		}
	}
	if (dynoff == 0 || dynsz == 0 ||
			dynoff > len || dynsz > len - dynoff)
		goto to_ident;

	needoffs = array_new();
	esz = is64 ? 16 : 8;
	for (i = 0; (uint64_t)(i + 1) * esz <= dynsz; i++) {
		const unsigned char *e   = d + dynoff + i * esz;
		uint64_t             tag = elf_needed_get(e, is64 ? 8 : 4, msb);
		uint64_t             val = elf_needed_get(e + (is64 ? 8 : 4),
												  is64 ? 8 : 4, msb);

		if (tag == 0)
			break;
		switch (tag) {
		case 1:
			array_append(needoffs, (void *)(uintptr_t)val);
			break;
		case 5:
			strvaddr = val;
			break;
		case 14:
			sonoff = val;
			hasson = true;
			break;
		default:
			break;
		}
	}

	if (strvaddr != 0) {
		for (i = 0; i < phnum; i++) {
			uint64_t po = phoff + (uint64_t)i * phentsize;
			uint64_t pt;
			uint64_t o;
			uint64_t va;
			uint64_t fs;

			if (po > len || phentsize > len - po)
				break;
			pt = elf_needed_get(d + po, 4, msb);
			o  = elf_needed_get(d + po + (is64 ?  8 :  4),
								is64 ? 8 : 4, msb);
			va = elf_needed_get(d + po + (is64 ? 16 :  8),
								is64 ? 8 : 4, msb);
			fs = elf_needed_get(d + po + (is64 ? 32 : 16),
								is64 ? 8 : 4, msb);

			if (pt == 1 && strvaddr >= va && strvaddr - va < fs) {
				stroff = o + (strvaddr - va);
				if (stroff >= len)
					stroff = 0;
				break;
			}
		}
	}

 to_ident:
	en = xzalloc(sizeof(*en));
	en->needed = array_new();
	for (i = 0; i < ARRAY_SIZE(elf_needed_machines); i++) {
		if (elf_needed_machines[i].em == em) {
			const char *sfx = elf_needed_suffix(em,
					elf_needed_machines[i].prefix, is64, flags);

			if (sfx != NULL)
				xasprintf(&en->arch, "%s_%s",
						  elf_needed_machines[i].prefix, sfx);
			break;
		}
	}
	if (stroff != 0) {
		const char *s;

		if (hasson) {
			s = elf_needed_str(buf, len, stroff + sonoff);
			if (s != NULL && *s != '\0')
				en->soname = xstrdup(s);
		}
		if (needoffs != NULL) {
			size_t n;
			void  *voff;

			array_for_each(needoffs, n, voff) {
				s = elf_needed_str(buf, len,
								   stroff + (uint64_t)(uintptr_t)voff);
				if (s != NULL && *s != '\0')
					array_append(en->needed, xstrdup(s));
			}
		}
	}

 out:
	if (needoffs != NULL)
		array_free(needoffs);
	free(buf);
	return en;
}

void
elf_needed_free(elf_needed *en)
{
	if (en == NULL)
		return;
	free(en->arch);
	free(en->soname);
	array_deepfree(en->needed, free);
	free(en);
}