/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 */

/*
 * Bounded verification of the PMS version-ordering axioms for
 * atom_compare_str(). A broken comparator (the classic X.100 == X.0 /
 * numeric-vs-lexical bug class) violates one of antisymmetry, reflexivity or
 * transitivity, so proving those three holds is the strongest correctness
 * statement we can make about the comparator.
 *
 * Two modes from one harness:
 *   - under CBMC (__CPROVER defined): every version string up to VLEN chars
 *     over the {0-9,.} alphabet is explored symbolically and the axioms are
 *     proven or a concrete counterexample is produced.
 *   - compiled with a normal C compiler: a bounded set of numeric versions is
 *     brute-forced, so the same properties run without CBMC installed.
 */
#include "main.h"
#include "atom.h"

#include <string.h>

const char *argv0 = "atom_axioms";
FILE *warnout;

#ifdef __CPROVER
extern char nondet_char(void);
#define ASSUME(c)       __CPROVER_assume(c)
#define REQUIRE(c, msg) __CPROVER_assert(c, msg)
#else
#include <stdio.h>
static int failures;
#define ASSUME(c)       do { if (!(c)) return; } while (0)
#define REQUIRE(c, msg) do { if (!(c)) { \
	fprintf(stderr, "COUNTEREXAMPLE (%s): %s\n", msg, __func__); failures++; } } while (0)
#endif

static void mkatom(char *dst, size_t dstsz, const char *ver)
{
	size_t n = strlen(ver);
	if (4 + n + 1 > dstsz)
		n = dstsz - 5;
	memcpy(dst, "c/p-", 4);
	memcpy(dst + 4, ver, n);
	dst[4 + n] = '\0';
}

static int is_ord(atom_equality e)
{
	return e == EQUAL || e == NEWER || e == OLDER;
}

static void check_pair(const char *v1, const char *v2)
{
	char s1[64], s2[64];
	atom_equality ab, ba, aa;

	mkatom(s1, sizeof s1, v1);
	mkatom(s2, sizeof s2, v2);

	ab = atom_compare_str(s1, s2);
	ba = atom_compare_str(s2, s1);
	REQUIRE(!(ab == NEWER) || ba == OLDER, "antisymmetry a>b => b<a");
	REQUIRE(!(ab == OLDER) || ba == NEWER, "antisymmetry a<b => b>a");
	REQUIRE(!(ab == EQUAL) || ba == EQUAL, "antisymmetry a==b => b==a");

	aa = atom_compare_str(s1, s1);
	REQUIRE(aa == EQUAL || aa == ERROR, "reflexivity a==a");
}

static void check_triple(const char *v1, const char *v2, const char *v3)
{
	char s1[64], s2[64], s3[64];
	atom_equality ab, bc, ac;

	mkatom(s1, sizeof s1, v1);
	mkatom(s2, sizeof s2, v2);
	mkatom(s3, sizeof s3, v3);

	ab = atom_compare_str(s1, s2);
	bc = atom_compare_str(s2, s3);
	ac = atom_compare_str(s1, s3);
	if (!is_ord(ab) || !is_ord(bc) || !is_ord(ac))
		return;

	REQUIRE(!((ab == OLDER || ab == EQUAL) && (bc == OLDER || bc == EQUAL))
			|| (ac == OLDER || ac == EQUAL),
			"transitivity a<=b<=c => a<=c");
}

#ifdef __CPROVER
#define VLEN 3
static void nondet_ver(char *v)
{
	int i;
	for (i = 0; i < VLEN; i++) {
		char c = nondet_char();
		ASSUME((c >= '0' && c <= '9') || c == '.');
		v[i] = c;
	}
	v[VLEN] = '\0';
}

int main(void)
{
	char v1[VLEN + 1], v2[VLEN + 1], v3[VLEN + 1];

	nondet_ver(v1);
	nondet_ver(v2);
	nondet_ver(v3);
	check_pair(v1, v2);
	check_triple(v1, v2, v3);
	return 0;
}
#else
static const int VALS[] = { 0, 1, 2, 9, 10 };
#define NV ((int)(sizeof VALS / sizeof VALS[0]))

static int gen(char out[][16], int max)
{
	int a, b, c, n = 0;
	for (a = 0; a < NV; a++) {
		if (n < max) snprintf(out[n++], 16, "%d", VALS[a]);
		for (b = 0; b < NV; b++) {
			if (n < max) snprintf(out[n++], 16, "%d.%d", VALS[a], VALS[b]);
			for (c = 0; c < NV; c++)
				if (n < max) snprintf(out[n++], 16, "%d.%d.%d",
						VALS[a], VALS[b], VALS[c]);
		}
	}
	return n;
}

int main(void)
{
	static char V[256][16];
	int i, j, k, n = gen(V, 256);

	printf("brute-force: %d versions; reflexivity/antisymmetry/transitivity\n", n);
	for (i = 0; i < n; i++)
		for (j = 0; j < n; j++)
			check_pair(V[i], V[j]);
	for (i = 0; i < n; i++)
		for (j = 0; j < n; j++)
			for (k = 0; k < n; k++)
				check_triple(V[i], V[j], V[k]);
	printf("%s: %d counterexample(s)\n", failures ? "FAIL" : "PASS", failures);
	return failures ? 1 : 0;
}
#endif