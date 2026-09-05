/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2026-     xx36x
 *
 * Fuzz the depclean dependency chooser in qmerge
 *
 * The chooser lives in file-private functions of qmerge.c, and the
 * environment setup in one of main.c, so both files are compiled into this
 * translation unit with main renamed;, build-dcx.sh links the rest of q
 * around it. Fuzz lane only, not part of the make check replay.
 */
#define main q_real_main
#include "../../main.c"
#undef main
#include "../../qmerge.c"

static char fuzz_base[4096];

static void
fuzz_wfile(const char *dir, const char *name, const char *content)
{
	char  p[8192];
	FILE *f;

	snprintf(p, sizeof(p), "%s/%s", dir, name);
	f = fopen(p, "w");
	if (f == NULL)
		return;
	fputs(content, f);
	fclose(f);
}

static void
fuzz_vdbpkg(const char *cat, const char *pf, const char *slot,
			const char *rdepend, const char *depend)
{
	char d[8192];
	char v[8192];

	snprintf(d, sizeof(d), "%s/root/var/db/pkg/%s", fuzz_base, cat);
	mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/root/var/db/pkg/%s/%s", fuzz_base, cat, pf);
	mkdir(d, 0755);
	snprintf(v, sizeof(v), "%s\n", slot);    fuzz_wfile(d, "SLOT", v);
	snprintf(v, sizeof(v), "%s\n", rdepend); fuzz_wfile(d, "RDEPEND", v);
	snprintf(v, sizeof(v), "%s\n", depend);  fuzz_wfile(d, "DEPEND", v);
	fuzz_wfile(d, "IDEPEND", "\n");
	fuzz_wfile(d, "PDEPEND", "\n");
	fuzz_wfile(d, "BDEPEND", "\n");
	fuzz_wfile(d, "KEYWORDS", "amd64\n");
	fuzz_wfile(d, "EAPI", "8\n");
	fuzz_wfile(d, "USE", "a\n");
	fuzz_wfile(d, "IUSE", "a b\n");
	snprintf(v, sizeof(v), "%s\n", cat);     fuzz_wfile(d, "CATEGORY", v);
	snprintf(v, sizeof(v), "%s\n", pf);      fuzz_wfile(d, "PF", v);
	fuzz_wfile(d, "COUNTER", "1\n");
	fuzz_wfile(d, "CONTENTS", "");
}

int LLVMFuzzerInitialize(int *argc, char ***argv);
int
LLVMFuzzerInitialize(int *argc, char ***argv)
{
	char d[8192];
	char cwd[4096];
	int  i;

	(void)argc;
	(void)argv;
	if (getcwd(cwd, sizeof(cwd)) == NULL)
		return 0;
	snprintf(fuzz_base, sizeof(fuzz_base), "%s/tests/r/tmp/fuzz_dcx", cwd);
	snprintf(d, sizeof(d), "%s/tests/r", cwd);                 mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/tests/r/tmp", cwd);             mkdir(d, 0755);
	mkdir(fuzz_base, 0755);
	snprintf(d, sizeof(d), "%s/root", fuzz_base);              mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/root/var", fuzz_base);          mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/root/var/db", fuzz_base);       mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/root/var/db/pkg", fuzz_base);   mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/root/var/lib", fuzz_base);      mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/root/var/lib/portage", fuzz_base); mkdir(d, 0755);
	fuzz_wfile(d, "world", "dc-libs/F\n");
	snprintf(d, sizeof(d), "%s/cfg", fuzz_base);               mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/cfg/etc", fuzz_base);           mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/cfg/etc/portage", fuzz_base);   mkdir(d, 0755);
	fuzz_wfile(d, "make.conf", "FEATURES=\"\"\n");
	fuzz_wfile(d, "package.mask", "=dc-libs/A-2\n");
	snprintf(d, sizeof(d), "%s/pkgdir", fuzz_base);            mkdir(d, 0755);
	snprintf(d, sizeof(d), "%s/tmp", fuzz_base);               mkdir(d, 0755);

	fuzz_vdbpkg("dc-libs", "A-1", "0", "", "");
	fuzz_vdbpkg("dc-libs", "A-2", "2", "", "");
	fuzz_vdbpkg("dc-libs", "B-1", "0", "", "");
	fuzz_vdbpkg("dc-libs", "C-1", "0/1", "dc-libs/B", "");
	fuzz_vdbpkg("dc-libs", "D-1", "0", "a? ( dc-libs/A:2 ) !a? ( dc-libs/B )", "");
	fuzz_vdbpkg("virtual", "v-1", "0", "|| ( dc-libs/A dc-libs/B )", "");
	fuzz_vdbpkg("virtual", "w-1", "0", "virtual/v", "");
	fuzz_vdbpkg("virtual", "x-1", "0", "virtual/y", "");
	fuzz_vdbpkg("virtual", "y-1", "0", "virtual/x", "");
	fuzz_vdbpkg("dc-libs", "F-1", "0", "", "");

	snprintf(d, sizeof(d), "%s/root", fuzz_base);   setenv("ROOT", d, 1);
	snprintf(d, sizeof(d), "%s/cfg", fuzz_base);    setenv("PORTAGE_CONFIGROOT", d, 1);
	snprintf(d, sizeof(d), "%s/pkgdir", fuzz_base); setenv("PKGDIR", d, 1);
	snprintf(d, sizeof(d), "%s/tmp", fuzz_base);    setenv("PORTAGE_TMPDIR", d, 1);
	setenv("QMERGE_NO_PHASES", "y", 1);

	warnout = stderr;
	argv0   = "fuzz_dcx";
	color_clear();
	overlays      = array_new();
	overlay_names = array_new();
	overlay_src   = array_new();
	for (i = 0; vars_to_read[i].name; ++i) {
		env_vars *var = &vars_to_read[i];

		switch (var->type) {
			case _Q_BOOL:  *var->value.b = var->default_value;          break;
			case _Q_STR:
			case _Q_NSTR:
			case _Q_ISTR:  *var->value.s = xstrdup(var->default_value); break;
			case _Q_ISET:  *var->value.t = (set *)q_deconst(var->default_value); break;
		}
		var->src = xstrdup(STR_DEFAULT);
	}
	set_portage_env_var(&vars_to_read[7], "true", "terminal");
	initialize_portage_env();
	warnout = fopen("/dev/null", "w");
	if (freopen("/dev/null", "w", stdout) == NULL)
		return 0;
	return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);
int
LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	struct qm_dc        dc;
	struct qm_dc_result res;
	array              *args;
	set                *use;
	char               *str;
	bool                full;

	if (size == 0 || size > 4096)
		return 0;
	args = array_new();
	use  = create_set();
	full = (data[0] & 1) != 0;
	str  = xmalloc(size);
	memcpy(str, data + 1, size - 1);
	str[size - 1] = '\0';
	add_set("a", use);
	add_set("b", use);
	if (full) {
		char  path[_Q_PATH_MAX];
		FILE *f;

		snprintf(path, sizeof(path), "%s%s/dc-libs/F-1/RDEPEND",
				 portroot, portvdb);
		if ((f = fopen(path, "w")) != NULL) {
			fprintf(f, "%s\n", str);
			fclose(f);
		}
	}
	if (qm_dc_load(&dc)) {
		if (full) {
			memset(&res, 0, sizeof(res));
			qm_dc_calc(&dc, args, &res);
			if (res.cleanlist != NULL)
				array_free(res.cleanlist);
		} else {
			array            *out    = array_new();
			struct qm_dc_pkg *parent = array_cnt(dc.pkgs) > 0 ?
					array_get(dc.pkgs, 0) : NULL;

			qm_dc_depcheck_str(&dc, str, use, parent, parent, out);
			array_deepfree(out, qm_dcx_free);
		}
		qm_dc_free(&dc);
	}
	free(str);
	free_set(use);
	array_free(args);
	return 0;
}