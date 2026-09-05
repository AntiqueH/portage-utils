#!/bin/bash
#
# Authors: antiqh, francoisb, marbit, xx36x, 0times
# Copyright same
# License: GPL v2
#
# testmycode.sh
#
# Run this from the portage-utils source root BEFORE opening a pull request.
# It runs the local sanity test suite ("check gates") from a clean build at every stage and exits
# non-zero if anything regresses.
#
# Usage:
#   ./testmycode.sh              run every default check gate (the pre-PR bar)
#   ./testmycode.sh TEST [...]   run only the named gate(s), e.g.
#                                ./testmycode.sh fuzz
#                                ./testmycode.sh fanalyzer valgrind
#   ./testmycode.sh list         print the check gates names and exit
#   ./testmycode.sh clean        remove tests/r/ (lane copies, logs, grown
#                                fuzz corpus, crash artifacts, kept failure
#                                scratch) and exit
#   ./testmycode.sh internal [TEST ...]
#                                every selected check gate
#                                (default set when none named) configures
#                                --enable-internal-libs, so q is built with
#                                the curl source tree in src/curl instead of
#                                the system libcurl. Needs src/curl/configure.
#                                static and m32 honour it too, giving the
#                                static+internal and m32+internal builds.
#   ./testmycode.sh valgrind chroot [DIR]
#                                run the valgrind gate inside a prepared
#                                chroot (default DIR:
#                                /home/work/sources/qmerge_chroot_x86_64_tests).
#                                The separate build is rsync -arA --delete'd to
#                                DIR/home/work/portage-utils first, then
#                                "testmycode.sh valgrind" runs in there.
#                                A chroot is needed because the host's
#                                AVX-512 glibc SIGILLs valgrind at _dl_start.
#                                Tthe chroot needs a stock glibc plus a build
#                                toolchain AND valgrind installed, /proc /sys
#                                /dev mounted, and /bin/bash present.
#                                The invoking user needs passwordless chroot
#                                entry, e.g. in /etc/sudoers.d/:
#                                  USER ALL=(root) NOPASSWD: /usr/bin/chroot \
#                                   /home/work/sources/qmerge_chroot_x86_64_tests \
#                                   /bin/bash -lc *
#                                (confirm the chroot path with command -v
#                                chroot; sudoers does no PATH lookup).
#
# Optional check gates (currently: warnings, tidy, m32, static, valgrind, fuzz, cbmc) are
# NOT run by the no-arg pass; name them explicitly to run one.
#
# Single-compiler hosts are handled like this: gcc-only check gates (gcc, warnings, opt, lto,
# c23, fanalyzer) SKIP where clang-only, and clang-only check gates (clang, tidy)
# SKIP where gcc-only. The fuzz gate uses clang+libFuzzer when clang is
# present, otherwise falls back to gcc+AFL++ (afl-gcc-fast), else SKIPs.
#
# Environment: CPU_JOBS=N build parallelism (default 30), FEATURES="..." the
# configure feature set, FUZZSECS=N seconds per fuzz target (default 30),
#
# The default CPU_JOBS assumes a big builder machine. The script detects the
# runner's CPU thread count at startup and prints a NOTE when the
# predefined CPU_JOBS exceeds it; set CPU_JOBS to your local thread count
# (nproc) in that case, e.g. CPU_JOBS="$(nproc)" ./testmycode.sh
# The detection needs nproc from sys-apps/coreutils installed.
#
# TESTMYCODE_VERBOSE=1 goes full verbose configure/build output to the terminal.
#
# TESTMYCODE_PARALLEL=1 runs the selected gates in up to 4 isolated build
# copies concurrently under tests/r/pN (override TESTMYCODE_PARALLEL_DIR;
# CPU_JOBS divided by 4; 0 = classic serial, single gate = serial). Every run
# records its full output under a stamped tests/r/logs/<date-time>/ dir.
# You'll find them there, since the output isn't always settled.
# Lane suites run with Q_SHORT_TMPDIR=1: suite scratch
# (ROOT, fixtures, gpg homes) goes to short /tmp mktemp dirs so gpg-agent
# sockets fit in sun_path, is removed on success, and is kept in
# tests/r/failed-<suite>/ on failure.
# 
# In parallel mode each copy restores its own default build and the main
# build copy is left untouched; in serial mode the build dir is left in a normal
# default build afterwards.
#
# Full-coverage package list:
# - sys-apps/coreutils
# - sys-devel/gcc
# - llvm-core/clang
# - app-arch/libarchive
# - app-crypt/libb2
# - sys-libs/zlib
# - app-crypt/gpgme
# - app-crypt/gnupg
# - net-misc/curl
# - net-misc/rsync
# - dev-util/cppcheck
# - dev-util/bear
# - dev-debug/valgrind
# - sci-mathematics/cbmc
# - app-forensics/aflplusplus
# - sys-apps/attr
# - app-arch/brotli
# - app-arch/bzip2
# - app-arch/gzip
# - app-arch/lz4
# - app-arch/lzip
# - app-arch/lzop
# - app-arch/xz-utils
# - app-arch/zstd
#
# Statically-built testing (the static tests) needs app-crypt/gpgme and
# dev-libs/libassuan built with USE=static-libs.
# 
# 32-bit testing (the m32 tests) needs the dependency libs built with
# abi_x86_32, which gentoo main overlay doesn't offer fully.
# those 32bit ABI ebuilds are in the same overlay.
# mostly these two:
# - app-crypt/gpgme[abi_x86_32,static-libs]::antiqh
# - dev-libs/libassuan[abi_x86_32,static-libs]::antiqh
#
# Install both from https://github.com/AntiqueH/antiqh-overlay, which also has sci-mathematics/cbmc 
# and app-forensics/aflplusplus.
# Our overlay contains debugging tools for C99/C++, and whatever you need
# to maintain and test your software.
# You're welcome, btw.
#
# The check gates, and how each presents itself.
# We call them "gates" instead of "tests", to make sure that these are gates before you propose PR.
#
#   gcc        GCC warnings+errors check gate (-O2, --enable-werror): every warning
#              in our own code becomes a hard error. -Werror is scoped via
#              CWFLAGS to portage-utils sources + libq only, so the vendored
#              (cloned) gnulib and curl builds never trip it. -O2 because many
#              diagnostics only fire with the optimizer on.
#   warnings   GCC warning "kitchen sink" over our built sources only
#              (non-built qglsa.c/template.c excluded), as errors: -Wall
#              -Wextra -Wshadow -Wcast-qual -Wwrite-strings -Wformat=2
#              -Wformat-overflow=2 -Wformat-truncation=2 -Wstringop-overflow=4
#              -Wnull-dereference -Wduplicated-cond -Wduplicated-branches
#              -Wlogical-op -Wvla -Walloca -Wmissing-prototypes
#              -Wold-style-definition, compiled at -O2 (many only fire with
#              the optimizer). A second, report-only pass counts the noisy
#              low-yield flags -Wpedantic/-Wundef (GNU variadic macros,
#              generated config.h probes) and -Wconversion/-Wsign-conversion
#              (size_t/int seams) as an INFO line without failing the check gate.
#   clang      The same check gate built with clang (different, wider warning set),
#              followed by "make check" so the suite also runs against the
#              clang-built binaries.
#   opt        Optimization check gate (-O3): surfaces optimization-only
#              diagnostics such as -Wmaybe-uninitialized.
#   lto        LTO + native ISA check gate (-O3 -flto -march=native) plus check:
#              cross-TU declaration/type mismatches (-Wlto-type-mismatch).
#   c23        C23 check gate (-std=c23) plus check: proves the C99 build is also
#              valid under the GCC 15 / recent Clang default standard, per
#              Porting to Modern C @ Gentoo.
#   asan       ASan+UBSan build and full "make check": use-after-free, heap
#              overflow, leaks, undefined behavior. The test that finds
#              and checks the real memory bugs in this build.
#   cppcheck   Static analysis over our sources only (SKIPs if the tool is
#              not installed).
#   fanalyzer  GCC static analyzer (-fanalyzer) over our sources only, as
#              errors: interprocedural symbolic execution catching leaks,
#              double-free, NULL derefs and fd leaks without running the
#              code. Vendored (cloned from external) dirs excluded.
#   tidy       clang-tidy bugprone-*/cert-*/clang-analyzer-* over our
#              sources, warnings-as-errors: a second, independent analyzer
#              beside fanalyzer (different engine, different blind spots).
#              Builds a compile_commands.json via bear first. SKIPs if
#              clang-tidy or bear is not installed.
#   heap       glibc heap hardening run: normal build, then "make check"
#              with MALLOC_CHECK_=3 MALLOC_PERTURB_=165 so stale-heap reads
#              and mild heap corruption become deterministic failures under
#              the production allocator (ASan replaces malloc, so this class
#              is otherwise untested).
#   valgrind   Full "make check" under valgrind memcheck via the build's own
#              Q_RUN_WITH_VALGRIND harness (tests/valgrind-wrapper):
#              uninitialized reads (which ASan cannot see), fd leaks and
#              origin tracking, on the unmodified binary. Built with
#              --disable-openmp so libgomp's thread-pool TLS (kept alive to
#              process exit). Passes clean in a stock-glibc chroot / CI runner.
#              SKIPs if valgrind is not installed.
#   m32        32-bit (-m32) build of q plus its correctness suites run
#              against the 32-bit binary. Adaptive: if a 32-bit gpgme links
#              (Gentoo multilib .pc in /usr/lib/pkgconfig) it builds the
#              FULL feature set (gpg/gpkg/gtree/qmanifest) and tests the gpg
#              eaters too (qxpak/qtbz2/qmanifest); otherwise it falls
#              back to core applets only (the common case: stock boxes have
#              no 32-bit gpgme/libassuan). Needs a 32-bit libcurl.pc in
#              /usr/lib/pkgconfig (curl[abi_x86_32]) unless the internal
#              modifier is on; SKIPs without it or without an -m32 toolchain.
#   static     Full-feature --enable-static build, statically-linked check,
#              then the whole test suite against the static binary. Links
#              the system libraries statically (libcurl.a from
#              curl[static-libs]); with the internal modifier it is the
#              static+internal build instead. SKIPs when the host lacks the
#              static dependency closure (configure hard-errors then).
#   fuzz       ASan+UBSan fuzzing of the remote-input parsers (atom strings,
#              dependency strings, CONTENTS lines, the Packages index, the
#              gpkg GLEP 74 Manifest + member layout) for FUZZSECS seconds
#              per target. A binhost is network input; this check gate feeds the
#              parsers hostile bytes. Engine: clang+libFuzzer when present,
#              else gcc+AFL++ (afl-gcc-fast + the AFL_DRIVER libFuzzer-compat
#              main), else SKIP. Leak checking is off here (that is asan's
#              job); crash inputs land in tests/r/artifacts/, the growing
#              corpus in tests/r/corpus/.
#   cbmc       Bounded verification of the PMS version-ordering axioms
#              (reflexivity, antisymmetry, transitivity) for atom_compare_str
#              via tests/cbmc/atom_axioms.c. The authoritative check is a
#              portable bounded brute-force over a numeric version set. When
#              'cbmc' is installed it also attempts symbolic proofs (timeout
#              CBMC_SECS, default 120s): the atom_explode-backed atom proof
#              is intractable for BMC and SKIPs on timeout, but the pure
#              xpak_data_bounds proof (tests/cbmc/xpak_bounds.c) converges =
#              a real PASS that the hostile-binhost data slice can never go
#              out of bounds. A genuine counterexample would FAIL.
#
# Check gates gcc/clang/opt/lto/c23 also apply the Gentoo "Modern C porting" flag
# set as errors (https://wiki.gentoo.org/wiki/Modern_C_porting):
# -Werror=implicit-function-declaration, -Werror=implicit-int,
# -Werror=int-conversion, -Werror=incompatible-pointer-types and
# -Werror=strict-prototypes.
#
# The most basic PARALLEL run:
#
#   CPU_JOBS="16" TESTMYCODE_PARALLEL=1 ./testmycode.sh
#
# runs the whole default check-gate set in up to 4 isolated test runs
# and prints each lane's summary at the end. Add optional gates by name
# for the full checks, e.g.:
#
#   CPU_JOBS="16" TESTMYCODE_PARALLEL=1 ./testmycode.sh gcc warnings clang opt lto \
#       c23 asan integer cppcheck fanalyzer tidy heap valgrind fuzz \
#       cbmc tsan flagmatrix
#
# GOTCHA: never run two instances in the same build dir concurrently. Every check gate
# starts with "make clean" and would destroy the other.
# NOTE 2: as before, we call "gates" to whatever checks we're doing to 'limit and stop'
# the program at a 'gate' when it's about to do bad stuff.
#

CPU_JOBS="${CPU_JOBS:-30}"
FUZZSECS="${FUZZSECS:-30}"
NCPU=$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 0)
HELP_END=$(awk 'NR>1 && !/^#/ {print NR-1; exit}' "$0")

jobs_advice() {
    if [ "$NCPU" -eq 0 ]; then
        printf 'NOTE: cannot detect the CPU thread count (need nproc from\n'
        printf '      sys-apps/coreutils); CPU_JOBS=%s stays as-is\n' "$CPU_JOBS"
    elif [ "$CPU_JOBS" -gt "$NCPU" ]; then
        printf 'NOTE: CPU_JOBS=%s but this system has only %s CPU threads;\n' \
            "$CPU_JOBS" "$NCPU"
        printf '      set the local value instead: CPU_JOBS=%s ./testmycode.sh ...\n' \
            "$NCPU"
    fi
}
read -ra FEATURES <<< "${FEATURES:---enable-qmanifest --enable-gpkg --enable-gtree}"
RESTORE_FEATURES=("${FEATURES[@]}")
SAN_CFLAGS="-O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined -fsanitize=pointer-compare,pointer-subtract -fsanitize-address-use-after-scope -fno-sanitize-recover=all"
SAN_LDFLAGS="-fsanitize=address,undefined"
INT_SAN="address,undefined,integer,implicit-conversion"
MODERN_C="-Werror=implicit-function-declaration -Werror=implicit-int -Werror=int-conversion -Werror=incompatible-pointer-types -Werror=strict-prototypes"
WARN_KITCHEN="-Wall -Wextra -Wshadow -Wcast-qual -Wwrite-strings -Wformat=2 -Wformat-overflow=2 -Wformat-truncation=2 -Wstringop-overflow=4 -Wnull-dereference -Wduplicated-cond -Wduplicated-branches -Wlogical-op -Wvla -Walloca -Wmissing-prototypes -Wold-style-definition -Werror"
WARN_ADVISORY="-Wpedantic -Wundef -Wconversion -Wsign-conversion"
# clang-tidy check set with bugprone/cert/clang-analyzer
TIDY_CHECKS="-*,bugprone-*,cert-*,clang-analyzer-*"
TIDY_CHECKS+=",-cert-err33-c,-cert-err34-c"
TIDY_CHECKS+=",-bugprone-unchecked-string-to-number-conversion"
TIDY_CHECKS+=",-bugprone-macro-parentheses,-bugprone-reserved-identifier"
TIDY_CHECKS+=",-cert-dcl37-c,-cert-dcl51-cpp"
TIDY_CHECKS+=",-bugprone-assignment-in-if-condition,-bugprone-inc-dec-in-conditions"
TIDY_CHECKS+=",-bugprone-easily-swappable-parameters"
TIDY_CHECKS+=",-bugprone-narrowing-conversions"
TIDY_CHECKS+=",-bugprone-multi-level-implicit-pointer-conversion"
TIDY_CHECKS+=",-bugprone-branch-clone"
TIDY_CHECKS+=",-clang-analyzer-security.insecureAPI.strcpy"
TIDY_CHECKS+=",-clang-analyzer-deadcode.DeadStores"
TIDY_CHECKS+=",-clang-analyzer-optin.performance.Padding"
TIDY_CHECKS+=",-bugprone-command-processor,-cert-env33-c"
TIDY_CHECKS+=",-clang-analyzer-optin.core.EnumCastOutOfRange"
# Analyzer/bugprone classes that produce only false positives on this
# tree.
TIDY_CHECKS+=",-clang-analyzer-security.ArrayBound"
TIDY_CHECKS+=",-clang-analyzer-unix.Stream"
TIDY_CHECKS+=",-clang-analyzer-unix.StdCLibraryFunctions"
TIDY_CHECKS+=",-clang-analyzer-core.NullDereference"
TIDY_CHECKS+=",-clang-analyzer-core.NonNullParamChecker"
TIDY_CHECKS+=",-clang-analyzer-core.StackAddressEscape"
TIDY_CHECKS+=",-clang-analyzer-optin.taint.GenericTaint"
TIDY_CHECKS+=",-bugprone-not-null-terminated-result"
TIDY_CHECKS+=",-bugprone-suspicious-missing-comma"
TIDY_CHECKS+=",-bugprone-suspicious-string-compare"
NONBUILT_SRC="qglsa.c template.c"
VG_CHROOT_DEFAULT="/home/work/sources/qmerge_chroot_x86_64_tests"
ALL_GATES=(gcc warnings clang opt lto c23 asan integer cppcheck fanalyzer tidy heap m32 static valgrind fuzz cbmc tsan flagmatrix)
OPTIONAL_GATES=(warnings tidy m32 static valgrind fuzz cbmc tsan flagmatrix)
FUZZ_TARGETS=(atom dep contents packages gpkg_manifest gpkg_structure envd binpath binrepos moves needed preserved usedep useflags xpak hash mfline elfneeded dcx)

HAVE_GCC=0;   command -v gcc   >/dev/null 2>&1 && HAVE_GCC=1
HAVE_CLANG=0; command -v clang >/dev/null 2>&1 && HAVE_CLANG=1
GCC_GATES="gcc warnings opt lto c23 fanalyzer"
CLANG_GATES="clang tidy integer"
AFL_DRIVER="${AFL_DRIVER:-/usr/lib64/afl/libAFLDriver.a}"

if [ -n "${TESTMYCODE_VERBOSE:-}" ] && [ "${TESTMYCODE_VERBOSE}" != 0 ]; then
    QOUT=/dev/stdout
else
    QOUT=/dev/null
fi

summary=()
rc=0

show() {
    printf '\n\033[1;34m==== %s ====\033[0m\n' "$*"
}

note() {
    summary+=("$(printf '%-5s %s' "$1" "$2")")
    [ "$1" = FAIL ] && rc=1
    return 0
}

gcc_gate() {
    show "check gate gcc: GCC warnings+errors+modern-C (-O2 -Werror)"
    make clean >>"$QOUT" 2>&1
    if ./configure --enable-werror "${FEATURES[@]}" CFLAGS="-O2 -g $MODERN_C" >>"$QOUT" 2>&1 \
            && make -j"$CPU_JOBS"; then
        note PASS "gcc -Werror -O2"
    else
        note FAIL "gcc -Werror -O2"
    fi
}

clang_gate() {
    show "check gate clang: Clang warnings+errors+modern-C (-O2 -Werror) + check"
    make clean >>"$QOUT" 2>&1
    if CC=clang ./configure --enable-werror "${FEATURES[@]}" CFLAGS="-O2 -g $MODERN_C" >>"$QOUT" 2>&1 \
            && make -j"$CPU_JOBS" CC=clang \
            && make check; then
        note PASS "clang -Werror -O2 + check"
    else
        note FAIL "clang -Werror -O2 + check"
    fi
}

opt_gate() {
    show "check gate opt: optimization + modern-C (-O3 -Werror)"
    make clean >>"$QOUT" 2>&1
    if ./configure --enable-werror "${FEATURES[@]}" CFLAGS="-O3 -g $MODERN_C" >>"$QOUT" 2>&1 \
            && make -j"$CPU_JOBS"; then
        note PASS "gcc -Werror -O3"
    else
        note FAIL "gcc -Werror -O3"
    fi
}

lto_gate() {
    show "check gate lto: LTO + native ISA (-O3 -flto -march=native -Werror) + check"
    make clean >>"$QOUT" 2>&1
    if ./configure --enable-werror "${FEATURES[@]}" \
            CFLAGS="-O3 -g -flto -march=native $MODERN_C" \
            LDFLAGS="-flto" AR=gcc-ar RANLIB=gcc-ranlib >/dev/null 2>&1 \
            && make -j"$CPU_JOBS" \
            && make check; then
        note PASS "gcc -flto -march=native + check"
    else
        note FAIL "gcc -flto -march=native + check"
    fi
}

c23_gate() {
    show "check gate c23: C23 (-std=c23 -Werror) + check"
    make clean >>"$QOUT" 2>&1
    if ./configure --enable-werror "${FEATURES[@]}" \
            CFLAGS="-O2 -g -std=c23 $MODERN_C" >/dev/null 2>&1 \
            && make -j"$CPU_JOBS" \
            && make check; then
        note PASS "gcc -std=c23 + check"
    else
        note FAIL "gcc -std=c23 + check"
    fi
}

asan_gate() {
    show "check gate asan: ASan+UBSan build and test suite (make check)"
    make clean >>"$QOUT" 2>&1
    if ./configure "${FEATURES[@]}" CFLAGS="$SAN_CFLAGS" LDFLAGS="$SAN_LDFLAGS" >>"$QOUT" 2>&1 \
            && make -j"$CPU_JOBS" \
            && ASAN_OPTIONS="detect_leaks=1:abort_on_error=1:strict_string_checks=1:detect_stack_use_after_return=1:quarantine_size_mb=512" \
               UBSAN_OPTIONS="print_stacktrace=1:halt_on_error=1" \
               make check; then
        note PASS "asan+ubsan make check"
    else
        note FAIL "asan+ubsan make check"
    fi
}

integer_gate() {
    show "check gate integer: Clang integer/implicit-conversion sanitizers + check"
    make clean >>"$QOUT" 2>&1
    local ilist=""
    [ -f "$PWD/.san-ignorelist" ] && ilist="-fsanitize-ignorelist=$PWD/.san-ignorelist"
    if CC=clang ./configure "${FEATURES[@]}" \
            CFLAGS="-O1 -g -fno-omit-frame-pointer -fsanitize=$INT_SAN -fno-sanitize-recover=all $ilist" \
            LDFLAGS="-fsanitize=$INT_SAN" >>"$QOUT" 2>&1 \
            && make -j"$CPU_JOBS" CC=clang \
            && ASAN_OPTIONS="detect_leaks=1:abort_on_error=1:strict_string_checks=1" \
               UBSAN_OPTIONS="print_stacktrace=1:halt_on_error=1" \
               make check; then
        note PASS "clang integer sanitizers + check"
    else
        note FAIL "clang integer sanitizers + check"
    fi
}


# Welcome to the USE flagomatrix check gate!
#
# (This is for absolute crazy users and developers. Use it with care.)
# (Don't loose your soul over it.)
#
fm_ok=1
fm_have_static=0
fm_have_static_curl=0
fm_have_internal=0

fm_build() {
    local name=$1 want_qman=$2 want_static=$3 want_internal=$4
    shift 4
    make clean >>"$QOUT" 2>&1
    if ! ./configure "$@" >>"$QOUT" 2>&1 || ! make -j"$CPU_JOBS" >>"$QOUT" 2>&1; then
        printf '  flagmatrix %-16s FAIL (build)\n' "$name"
        fm_ok=0
        return 1
    fi
    if [ "$want_qman" = 1 ]; then
        if ! ./q -h 2>/dev/null | grep -qw qmanifest; then
            printf '  flagmatrix %-16s FAIL (qmanifest applet missing)\n' "$name"
            fm_ok=0
            return 1
        fi
    else
        if ./q -h 2>/dev/null | grep -qw qmanifest; then
            printf '  flagmatrix %-16s FAIL (qmanifest applet present)\n' "$name"
            fm_ok=0
            return 1
        fi
    fi
    if [ "$want_static" = 1 ] && ! file ./q | grep -q "statically linked"; then
        printf '  flagmatrix %-16s FAIL (not statically linked)\n' "$name"
        fm_ok=0
        return 1
    fi
    if [ "$want_static" = 0 ]; then
        if [ "$want_internal" = 0 ] && ! ldd ./q 2>/dev/null | grep -q libcurl; then
            printf '  flagmatrix %-16s FAIL (system libcurl not linked)\n' "$name"
            fm_ok=0
            return 1
        fi
        if [ "$want_internal" = 1 ] && ldd ./q 2>/dev/null | grep -q libcurl; then
            printf '  flagmatrix %-16s FAIL (internal build links libcurl.so)\n' "$name"
            fm_ok=0
            return 1
        fi
    fi
    mkdir -p .flagmatrix
    cp ./q ".flagmatrix/q.${name}"
    strip ".flagmatrix/q.${name}" 2>/dev/null
    printf '%s\t%s\t%s bytes\t%s\n' "$name" \
        "$([ "$want_static" = 1 ] && printf static || printf dynamic)" \
        "$(stat -c %s ".flagmatrix/q.${name}")" "$*" \
        >> .flagmatrix/manifest.txt
    printf '  flagmatrix %-16s ok\n' "$name"
    return 0
}

flagmatrix_gate() {
    show "check gate flagmatrix: feature-flag combination builds"
    fm_ok=1
    fm_have_static=0
    fm_have_static_curl=0
    fm_have_internal=0
    rm -rf .flagmatrix
    printf 'int main(void){return 0;}\n' > .fm_probe.c
    ${CC:-gcc} -static .fm_probe.c -o .fm_probe >/dev/null 2>&1 && fm_have_static=1
    rm -f .fm_probe .fm_probe.c
    if pkg-config --static --exists libcurl 2>/dev/null \
            && [ -f "$(pkg-config --variable=libdir libcurl 2>/dev/null)/libcurl.a" ]; then
        fm_have_static_curl=1
    fi
    [ -f src/curl/configure ] && fm_have_internal=1

    if [ "${FLAGMATRIX:-}" = full ]; then
        local gpg qman gtree gpkg omp st ic args
        for gpg in 0 1; do
        for qman in 0 1; do
        for gtree in 0 1; do
            if [ "$gpg" = 0 ] && { [ "$qman" = 1 ] || [ "$gtree" = 1 ]; }; then
                continue
            fi
        for gpkg in 0 1; do
        for omp in 0 1; do
        for st in 0 1; do
            if [ "$st" = 1 ] && [ "$fm_have_static" = 0 ]; then
                continue
            fi
        for ic in 0 1; do
            if [ "$ic" = 1 ] && [ "$fm_have_internal" = 0 ]; then
                continue
            fi
            if [ "$st" = 1 ] && [ "$ic" = 0 ] && [ "$fm_have_static_curl" = 0 ]; then
                continue
            fi
            args=()
            if [ "$gpg" = 1 ]; then
                args+=(--enable-gpg)
            else
                args+=(--disable-gpg)
            fi
            if [ "$qman" = 1 ]; then
                args+=(--enable-qmanifest)
            else
                args+=(--disable-qmanifest)
            fi
            if [ "$gtree" = 1 ]; then
                args+=(--enable-gtree)
            else
                args+=(--disable-gtree)
            fi
            if [ "$gpkg" = 1 ]; then
                args+=(--enable-gpkg)
            else
                args+=(--disable-gpkg)
            fi
            if [ "$omp" = 1 ]; then
                args+=(--enable-openmp)
            else
                args+=(--disable-openmp)
            fi
            [ "$st" = 1 ] && args+=(--enable-static)
            [ "$ic" = 1 ] && args+=(--enable-internal-libs)
            fm_build "g${gpg}m${qman}t${gtree}p${gpkg}o${omp}s${st}i${ic}" \
                "$qman" "$st" "$ic" "${args[@]}"
        done
        done
        done
        done
        done
        done
        done
    else
        fm_build all-on      1 0 0 --enable-gpg --enable-qmanifest \
            --enable-gtree --enable-gpkg --enable-openmp
        fm_build minimal     0 0 0 --disable-gpg --disable-openmp
        fm_build no-gpg      0 0 0 --disable-gpg --enable-gpkg
        fm_build no-gpkg     1 0 0 --enable-qmanifest --enable-gtree
        fm_build no-gtree    1 0 0 --enable-qmanifest --enable-gpkg
        fm_build no-qmanifest 0 0 0 --disable-qmanifest --enable-gtree \
            --enable-gpkg
        fm_build no-openmp   1 0 0 --enable-qmanifest --enable-gtree \
            --enable-gpkg --disable-openmp
        fm_build gpg-only    0 0 0 --enable-gpg --disable-qmanifest
        if [ "$fm_have_static" = 0 ]; then
            printf '  flagmatrix %-16s skipped (no static libc)\n' static-min
        elif [ "$fm_have_static_curl" = 0 ]; then
            printf '  flagmatrix %-16s skipped (no static libcurl)\n' static-min
        else
            fm_build static-min 0 1 0 --enable-static --disable-gpg \
                --disable-openmp
        fi
        if [ "$fm_have_internal" = 1 ]; then
            fm_build internal-on  1 0 1 --enable-qmanifest --enable-gtree \
                --enable-gpkg --enable-internal-libs
            fm_build internal-min 0 0 1 --disable-gpg --disable-openmp \
                --enable-internal-libs
            if [ "$fm_have_static" = 1 ]; then
                fm_build static-internal 0 1 1 --enable-static --disable-gpg \
                    --disable-openmp --enable-internal-libs
            else
                printf '  flagmatrix %-16s skipped (no static libc)\n' static-internal
            fi
        else
            printf '  flagmatrix %-16s skipped (no src/curl/configure)\n' internal
        fi
    fi

    if [ "$fm_ok" -eq 1 ]; then
        note PASS "flagmatrix feature-combination builds"
    else
        note FAIL "flagmatrix feature-combination builds"
    fi
}

tsan_gate() {
    show "check gate tsan: ThreadSanitizer build and test suite (make check)"
    make clean >>"$QOUT" 2>&1
    local tsup=""
    [ -f "$PWD/.tsan-suppressions" ] && tsup=":suppressions=$PWD/.tsan-suppressions"
    if ./configure "${FEATURES[@]}" \
            CFLAGS="-O1 -g -fno-omit-frame-pointer -fsanitize=thread" \
            LDFLAGS="-fsanitize=thread" >>"$QOUT" 2>&1 \
            && make -j"$CPU_JOBS" \
            && TSAN_OPTIONS="halt_on_error=1:second_deadlock_stack=1${tsup}" \
               make check; then
        note PASS "tsan make check"
    else
        note FAIL "tsan make check"
    fi
}

cppcheck_gate() {
    show "check gate cppcheck: static analysis"
    if ! command -v cppcheck >/dev/null 2>&1; then
        note SKIP "cppcheck (not installed)"
        return 0
    fi
    make clean >>"$QOUT" 2>&1
    if ! ./configure "${FEATURES[@]}" >>"$QOUT" 2>&1; then
        note FAIL "cppcheck (configure)"
        return 0
    fi
    if cppcheck --std=c99 --quiet -j "$CPU_JOBS" \
            --inline-suppr --error-exitcode=2 \
            --suppressions-list=.cppcheck-suppressions \
            --suppress=missingIncludeSystem --suppress=unmatchedSuppression \
            -i src/curl -i autotools/gnulib -I libq -I . ./*.c libq/*.c; then
        note PASS "cppcheck"
    else
        note FAIL "cppcheck"
    fi
}

fanalyzer_gate() {
    show "check gate fanalyzer: GCC static analyzer over our sources (-fanalyzer -Werror)"
    make clean >>"$QOUT" 2>&1
    if ! ./configure "${FEATURES[@]}" >>"$QOUT" 2>&1; then
        note FAIL "fanalyzer (configure)"
        return 0
    fi
    local gpgme_cflags
    gpgme_cflags=$(pkg-config --cflags gpgme 2>/dev/null || gpgme-config --cflags 2>/dev/null || :)
    if our_sources | tr '\n' '\0' | xargs -0 -n1 -P"$CPU_JOBS" \
            gcc -fanalyzer -fsyntax-only -O2 -Werror \
                -DHAVE_CONFIG_H -I. -Ilibq -Iautotools/gnulib \
                $(curl_cflags) $gpgme_cflags; then
        note PASS "gcc -fanalyzer"
    else
        note FAIL "gcc -fanalyzer"
    fi
}

our_sources() {
    local f b
    for f in ./*.c libq/*.c; do
        b=${f##*/}
        case " $NONBUILT_SRC " in *" $b "*) continue ;; esac
        printf '%s\n' "$f"
    done
}

curl_cflags() {
    if [ "$want_internal" -eq 1 ]; then
        printf -- '-Isrc/curl/include -DCURL_STATICLIB'
    else
        pkg-config --cflags libcurl 2>/dev/null || :
    fi
}

warnings_gate() {
    show "check gate warnings: GCC warning kitchen-sink over our sources (-Werror)"
    make clean >>"$QOUT" 2>&1
    if ! ./configure "${FEATURES[@]}" >>"$QOUT" 2>&1; then
        note FAIL "warnings (configure)"
        return 0
    fi
    local gpgme_cflags inc adv
    gpgme_cflags=$(pkg-config --cflags gpgme 2>/dev/null || gpgme-config --cflags 2>/dev/null || :)
    inc="-fopenmp -DHAVE_CONFIG_H -I. -Ilibq -Iautotools/gnulib $(curl_cflags) $gpgme_cflags"
    if our_sources | tr '\n' '\0' | xargs -0 -n1 -P"$CPU_JOBS" \
            gcc $WARN_KITCHEN $MODERN_C -O2 -c -o /dev/null $inc; then
        note PASS "gcc warning kitchen-sink"
    else
        note FAIL "gcc warning kitchen-sink"
    fi
    adv=$(our_sources | tr '\n' '\0' | xargs -0 -n1 -P"$CPU_JOBS" \
            gcc $WARN_ADVISORY -O2 -fsyntax-only $inc 2>&1 \
            | grep -c 'warning:')
    note INFO "advisory warnings (pedantic/undef/conversion): $adv (report-only)"
}

tidy_gate() {
    show "check gate tidy: clang-tidy (bugprone/cert/clang-analyzer) over our sources"
    if ! clang-tidy --version >/dev/null 2>&1; then
        note SKIP "tidy (clang-tidy not installed or not runnable)"
        return 0
    fi
    if ! bear --version >/dev/null 2>&1; then
        note SKIP "tidy (bear not installed or not runnable)"
        return 0
    fi
    make clean >>"$QOUT" 2>&1
    if ! ./configure "${FEATURES[@]}" >>"$QOUT" 2>&1 \
            || ! bear -- make -j"$CPU_JOBS" >>"$QOUT" 2>&1; then
        note FAIL "tidy (compile-db build)"
        return 0
    fi
    local tidy_extra=(--extra-arg=-isystem"$PWD/autotools/gnulib")
    [ -d src/curl/include ] && tidy_extra+=(--extra-arg=-isystem"$PWD/src/curl/include")
    # One clang-tidy process per file.
    if our_sources | xargs -n1 -P "$CPU_JOBS" \
            clang-tidy -p . --quiet --checks="$TIDY_CHECKS" \
            --warnings-as-errors="$TIDY_CHECKS" \
            --header-filter='.*' \
            --exclude-header-filter='(config\.h|autotools/gnulib|src/curl)' \
            "${tidy_extra[@]}"; then
        note PASS "clang-tidy"
    else
        note FAIL "clang-tidy"
    fi
}

heap_gate() {
    show "check gate heap: glibc MALLOC_CHECK_/MALLOC_PERTURB_ test suite"
    make clean >>"$QOUT" 2>&1
    if ./configure "${FEATURES[@]}" CFLAGS="-O1 -g" >>"$QOUT" 2>&1 \
            && make -j"$CPU_JOBS" \
            && MALLOC_CHECK_=3 MALLOC_PERTURB_=165 make check; then
        note PASS "glibc heap-hardened make check"
    else
        note FAIL "glibc heap-hardened make check"
    fi
}

valgrind_chroot_gate() {
    local dir="$1" dst
    show "check gate valgrind (chroot): memcheck inside $dir"
    printf 'NOTE: the chroot must ALREADY have /proc /sys /dev mounted;\n'
    printf 'NOTE: the invoking user must be able to enter the chroot as\n'
    printf '      root without a password (/etc/sudoers.d/ NOPASSWD rule\n'
    printf '      or a polkit grant).\n'
    if [ ! -x "$dir/bin/bash" ]; then
        note SKIP "valgrind chroot ($dir has no /bin/bash; not a chroot?)"
        return 0
    fi
    if ! command -v rsync >/dev/null 2>&1; then
        note SKIP "valgrind chroot (rsync not installed)"
        return 0
    fi
    dst="$dir/home/work/portage-utils"
    if ! mkdir -p "$dst" 2>/dev/null && ! sudo mkdir -p "$dst"; then
        note FAIL "valgrind chroot (cannot create $dst)"
        return 0
    fi
    if ! rsync -arA --delete --exclude=.docker --exclude=.git ./ "$dst/"; then
        note FAIL "valgrind chroot (rsync to $dst)"
        return 0
    fi
    if sudo chroot "$dir" /bin/bash -lc \
            "cd /home/work/portage-utils && ./testmycode.sh valgrind"; then
        note PASS "valgrind make check (chroot)"
    else
        note FAIL "valgrind make check (chroot)"
    fi
}

valgrind_gate() {
    show "check gate valgrind: test suite under valgrind memcheck"
    if ! command -v valgrind >/dev/null 2>&1; then
        note SKIP "valgrind (not installed)"
        return 0
    fi
    make clean >>"$QOUT" 2>&1
    if ! ./configure "${FEATURES[@]}" --disable-openmp CFLAGS="-O1 -g" >>"$QOUT" 2>&1 \
            || ! make -j"$CPU_JOBS"; then
        note FAIL "valgrind (build)"
        return 0
    fi
    local vgfd probe reason
    vgfd=4096
    [ "$(ulimit -Hn)" -lt "$vgfd" ] && vgfd=$(ulimit -Hn)
    probe=$( ulimit -Sn "$vgfd" 2>/dev/null
             valgrind --error-exitcode=234 ./q -V 2>&1 )
    reason=$(printf '%s\n' "$probe" | grep -m1 -oE \
        'unhandled instruction bytes.*|Unrecognised instruction.*|Valgrind: FATAL:.*|Illegal opcode.*|signal 4 \(SIGILL\).*')
    if [ -n "$reason" ]; then
        note SKIP "valgrind (cannot run on this host: $reason)"
        return 0
    fi
    if ( ulimit -Sn "$vgfd" 2>/dev/null
         Q_RUN_WITH_VALGRIND=1 GITHUB_JOB=valgrind make check ); then
        note PASS "valgrind make check"
    else
        note FAIL "valgrind make check"
    fi
}

fuzz_gate() {
    # regenerate the documented crash reproducers into the seed corpus
    sh tests/fuzz/mkregress.sh
    # Set the libFuzzer (clang). fall back to gcc+AFL++ (afl-gcc-fast + the
    # AFL_DRIVER libFuzzer-compat main). SKIP if neither engine is present.
    if [ "$HAVE_CLANG" -eq 1 ]; then
        fuzz_gate_libfuzzer
    elif command -v afl-gcc-fast >/dev/null 2>&1 && [ -f "$AFL_DRIVER" ]; then
        fuzz_gate_afl
    else
        show "check gate fuzz: fuzzing the remote-input parsers"
        note SKIP "fuzz (need clang+libFuzzer, or afl-gcc-fast + $AFL_DRIVER)"
    fi
}

fuzz_gate_libfuzzer() {
    show "check gate fuzz: libFuzzer on the remote-input parsers (${FUZZSECS}s per target)"
    if ! command -v clang >/dev/null 2>&1; then
        note SKIP "fuzz (clang not installed)"
        return 0
    fi
    make clean >>"$QOUT" 2>&1
    if ! CC=clang ./configure "${FEATURES[@]}" --disable-openmp \
            CFLAGS="-O1 -g -fsanitize=address,undefined -fsanitize=fuzzer-no-link -fno-sanitize-recover=all" \
            LDFLAGS="-fsanitize=address,undefined" >/dev/null 2>&1 \
            || ! make -j"$CPU_JOBS" CC=clang; then
        note FAIL "fuzz (instrumented build)"
        return 0
    fi
    local gpgme_cflags t ok=1
    local built=()
    gpgme_cflags=$(pkg-config --cflags gpgme 2>/dev/null || gpgme-config --cflags 2>/dev/null || :)
    mkdir -p tests/fuzz/.bin tests/r/artifacts tests/r/tmp
    for t in "${FUZZ_TARGETS[@]}"; do
        mkdir -p "tests/r/corpus/$t"
        if [ "$t" = dcx ]; then
            if CC=clang FUZZ_CFLAGS="-fsanitize=fuzzer,address,undefined -O1 -g" \
                    OUT=tests/fuzz/.bin tests/fuzz/build-dcx.sh >>"$QOUT" 2>&1; then
                built+=("$t")
            else
                printf 'fuzz_dcx: harness build failed\n' >&2
                ok=0
            fi
            continue
        fi
        if ! clang -fsanitize=fuzzer,address,undefined -O1 -g \
                -DHAVE_CONFIG_H -I. -Ilibq -Iautotools/gnulib $gpgme_cflags \
                "tests/fuzz/fuzz_$t.c" \
                libq/libq.a autotools/gnulib/libgnu.a \
                -larchive -lz -lb2 \
                -o "tests/fuzz/.bin/fuzz_$t"; then
            printf 'fuzz_%s: harness build failed\n' "$t" >&2
            ok=0
            continue
        fi
        built+=("$t")
    done
    local fpar="$CPU_JOBS" bi bn bt
    [ "$fpar" -gt 4 ] && fpar=4
    [ "$fpar" -lt 1 ] && fpar=1
    for ((bi = 0; bi < ${#built[@]}; bi += fpar)); do
        local pids=() names=()
        for bt in "${built[@]:bi:fpar}"; do
            (
                dictarg=()
                [ -f "tests/fuzz/dict/$bt.dict" ] && \
                    dictarg=("-dict=tests/fuzz/dict/$bt.dict")
                regress=()
                [ -d "tests/fuzz/regressions/$bt" ] && \
                    regress=("tests/fuzz/regressions/$bt")
                ASAN_OPTIONS="detect_leaks=0" \
                    TMPDIR="$PWD/tests/r/tmp" \
                    "tests/fuzz/.bin/fuzz_$bt" \
                    -max_total_time="$FUZZSECS" -print_final_stats=1 \
                    -timeout=25 -print_funcs=0 \
                    "${dictarg[@]}" \
                    -artifact_prefix="tests/r/artifacts/${bt}-" \
                    "tests/r/corpus/$bt" "tests/fuzz/seeds/$bt" \
                    "${regress[@]}"
            ) >"tests/r/artifacts/$bt.gatelog" 2>&1 &
            pids+=($!)
            names+=("$bt")
        done
        for bn in "${!pids[@]}"; do
            if ! wait "${pids[$bn]}"; then
                printf 'fuzz_%s: FAILED, reproducer in tests/r/artifacts/\n' \
                    "${names[$bn]}" >&2
                ok=0
            fi
            cat "tests/r/artifacts/${names[$bn]}.gatelog"
        done
    done
    if [ "$ok" -eq 1 ]; then
        note PASS "fuzz (${FUZZ_TARGETS[*]})"
    else
        note FAIL "fuzz (${FUZZ_TARGETS[*]})"
    fi
}

fuzz_gate_afl() {
    show "check gate fuzz: AFL++ (afl-gcc-fast) on the remote-input parsers (${FUZZSECS}s per target)"
    make clean >>"$QOUT" 2>&1
    if ! AFL_QUIET=1 CC=afl-gcc-fast ./configure "${FEATURES[@]}" --disable-openmp \
            CFLAGS="-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all" \
            LDFLAGS="-fsanitize=address,undefined" >/dev/null 2>&1 \
            || ! AFL_QUIET=1 make -j"$CPU_JOBS" CC=afl-gcc-fast; then
        note FAIL "fuzz (afl instrumented build)"
        return 0
    fi
    local gpgme_cflags t ok=1
    local regress
    gpgme_cflags=$(pkg-config --cflags gpgme 2>/dev/null || gpgme-config --cflags 2>/dev/null || :)
    mkdir -p tests/fuzz/.bin tests/r/artifacts tests/r/tmp
    for t in "${FUZZ_TARGETS[@]}"; do
        mkdir -p "tests/r/corpus/$t"
        if ! AFL_QUIET=1 afl-gcc-fast -O1 -g -fsanitize=address,undefined \
                -DHAVE_CONFIG_H -I. -Ilibq -Iautotools/gnulib $gpgme_cflags \
                "tests/fuzz/fuzz_$t.c" "$AFL_DRIVER" \
                libq/libq.a autotools/gnulib/libgnu.a \
                -larchive -lz -lb2 \
                -o "tests/fuzz/.bin/fuzz_$t"; then
            printf 'fuzz_%s: afl harness build failed\n' "$t" >&2
            ok=0
            continue
        fi
        regress=()
        [ -d "tests/fuzz/regressions/$t" ] && regress=("tests/fuzz/regressions/$t")
        if ! ASAN_OPTIONS="detect_leaks=0" \
                TMPDIR="$PWD/tests/r/tmp" \
                "tests/fuzz/.bin/fuzz_$t" \
                -max_total_time="$FUZZSECS" \
                -artifact_prefix="tests/r/artifacts/${t}-" \
                "tests/r/corpus/$t" "tests/fuzz/seeds/$t" "${regress[@]}"; then
            printf 'fuzz_%s: FAILED (afl), reproducer in tests/r/artifacts/\n' "$t" >&2
            ok=0
        fi
    done
    if [ "$ok" -eq 1 ]; then
        note PASS "fuzz/afl (${FUZZ_TARGETS[*]})"
    else
        note FAIL "fuzz/afl (${FUZZ_TARGETS[*]})"
    fi
}

# Full-feature --enable-static build with the whole suite run against the
# static binary. Links the system libraries statically, so it needs
# curl[static-libs]; with the internal configs it is the static+internal
# build instead. configure itself hard-errors when -static cannot link or
# no static libcurl exists, so a host without the static dep closure
# SKIPs at that stage. a failure past configure is a regression.
static_gate() {
    show "check gate static: full-feature --enable-static build + make check"
    printf 'int main(void){return 0;}\n' > .st_probe.c
    if ! ${CC:-gcc} -static .st_probe.c -o .st_probe >/dev/null 2>&1; then
        rm -f .st_probe .st_probe.c
        note SKIP "static (no static libc)"
        return 0
    fi
    rm -f .st_probe .st_probe.c
    local st_args=(--enable-static --enable-qmanifest --enable-gpkg --enable-gtree)
    [ "$want_internal" -eq 1 ] && st_args+=(--enable-internal-libs)
    make clean >>"$QOUT" 2>&1
    if ! ./configure "${st_args[@]}" >>"$QOUT" 2>&1; then
        note SKIP "static (static dep closure not linkable on this host)"
        return 0
    fi
    if ! make -j"$CPU_JOBS" >>"$QOUT" 2>&1; then
        note FAIL "static (build)"
        return 0
    fi
    if ! file ./q | grep -q "statically linked"; then
        note FAIL "static (binary not statically linked)"
        return 0
    fi
    if make check; then
        note PASS "static --enable-static make check"
    else
        note FAIL "static --enable-static make check"
    fi
}

m32_gate() {
    show "check gate m32: 32-bit (-m32) build + suites"
    local probe
    probe=$(mktemp 2>/dev/null || echo ./.m32probe)
    if ! printf 'int main(void){return 0;}\n' | gcc -m32 -x c - -o "$probe" 2>/dev/null; then
        rm -f "$probe"
        note SKIP "m32 (no -m32/multilib toolchain)"
        return 0
    fi
    local m32pc=/usr/lib/pkgconfig gpg_ok=0 cf lf
    local m32_args=()
    if [ "$want_internal" -eq 1 ]; then
        m32_args+=(--enable-internal-libs)
    elif ! PKG_CONFIG_PATH="$m32pc" PKG_CONFIG_LIBDIR="$m32pc" \
            pkg-config --exists libcurl 2>/dev/null; then
        rm -f "$probe"
        note SKIP "m32 (no 32-bit libcurl.pc in $m32pc)"
        return 0
    fi
    # Detect a 32-bit gpgme stack: Gentoo multilib installs the i386 .pc
    # files in /usr/lib/pkgconfig. If a -m32 program links against gpgme,
    # the full feature set (gpg/gpkg/gtree/qmanifest) is buildable 32-bit
    # and we test the gpg users too. Otherwise fall back to core
    # applets only (those without gpgme).
    if PKG_CONFIG_PATH="$m32pc" PKG_CONFIG_LIBDIR="$m32pc" \
            pkg-config --exists gpgme 2>/dev/null; then
        cf=$(PKG_CONFIG_PATH="$m32pc" PKG_CONFIG_LIBDIR="$m32pc" pkg-config --cflags gpgme 2>/dev/null)
        lf=$(PKG_CONFIG_PATH="$m32pc" PKG_CONFIG_LIBDIR="$m32pc" pkg-config --libs gpgme 2>/dev/null)
        printf 'int main(void){return 0;}\n' \
            | gcc -m32 $cf -x c - $lf -o "$probe" 2>/dev/null && gpg_ok=1
    fi
    rm -f "$probe"

    make clean >>"$QOUT" 2>&1
    local mode tests built=0
    if [ "$gpg_ok" -eq 1 ]; then
        if PKG_CONFIG_PATH="$m32pc" PKG_CONFIG_LIBDIR="$m32pc" \
                ./configure --enable-qmanifest --enable-gpkg --enable-gtree \
                    --disable-openmp "${m32_args[@]}" \
                    CFLAGS='-m32 -O2 -g' LDFLAGS='-m32' >/dev/null 2>&1 \
                && make -j"$CPU_JOBS" >>"$QOUT" 2>&1; then
            mode="full (gpg/gpkg/gtree/qmanifest)"
            tests="atom_compare atom_explode qatom rmspace copy_file mkdir qxpak qtbz2 qmanifest"
            built=1
        else
            printf 'm32: full 32-bit build failed, falling back to minimal\n' >&2
            make clean >>"$QOUT" 2>&1
        fi
    fi
    if [ "$built" -eq 0 ]; then
        if PKG_CONFIG_PATH="$m32pc" PKG_CONFIG_LIBDIR="$m32pc" \
                ./configure --disable-gpg --disable-qmanifest --disable-gtree --disable-gpkg \
                    --disable-openmp "${m32_args[@]}" \
                    CFLAGS='-m32 -O2 -g' LDFLAGS='-m32' >/dev/null 2>&1 \
                && make -j"$CPU_JOBS" >>"$QOUT" 2>&1; then
            mode="minimal (core applets; no 32-bit gpgme)"
            tests="atom_compare atom_explode qatom rmspace copy_file mkdir"
            built=1
        fi
    fi
    if [ "$built" -eq 0 ]; then
        note FAIL "m32 (build)"
        return 0
    fi
    if ! file ./q 2>/dev/null | grep -q 'ELF 32-bit'; then
        note FAIL "m32 (not a 32-bit binary)"
        return 0
    fi
    local t ok=1
    for t in $tests; do
        [ -d "tests/$t" ] || continue
        make -C "tests/$t" check >/dev/null 2>&1 || { printf 'm32: tests/%s failed\n' "$t" >&2; ok=0; }
    done
    if [ "$ok" -eq 1 ]; then
        note PASS "m32 32-bit build + suites [$mode]"
    else
        note FAIL "m32 32-bit suites [$mode]"
    fi
}

cbmc_gate() {
    show "check gate cbmc: bounded verification of atom ordering axioms + xpak bounds"
    make clean >>"$QOUT" 2>&1
    if ! ./configure "${FEATURES[@]}" CFLAGS="-O1 -g" >>"$QOUT" 2>&1 \
            || ! make -j"$CPU_JOBS" >>"$QOUT" 2>&1; then
        note FAIL "cbmc (build)"
        return 0
    fi
    local gpgme_cflags inc bin
    gpgme_cflags=$(pkg-config --cflags gpgme 2>/dev/null || gpgme-config --cflags 2>/dev/null || :)
    inc="-DHAVE_CONFIG_H -I. -Ilibq -Iautotools/gnulib $(curl_cflags) $gpgme_cflags"
    bin="tests/cbmc/.atom_axioms"
    if gcc -O1 -g $inc tests/cbmc/atom_axioms.c \
            libq/libq.a autotools/gnulib/libgnu.a -larchive -lz -lb2 -o "$bin" 2>/dev/null \
            && "$bin"; then
        note PASS "atom axioms (bounded brute-force)"
    else
        note FAIL "atom axioms (bounded brute-force)"
    fi
    if command -v cbmc >/dev/null 2>&1; then
        local cbmc_secs="${CBMC_SECS:-120}" rc2=0
        timeout "$cbmc_secs" cbmc --unwind 16 --unwinding-assertions \
                --bounds-check --pointer-check \
                $inc tests/cbmc/atom_axioms.c libq/atom.c libq/rmspace.c \
                >/dev/null 2>&1 || rc2=$?
        case "$rc2" in
            0)   note PASS "cbmc atom axioms (symbolic proof)" ;;
            124) note SKIP "cbmc atom symbolic proof (atom_explode parser intractable for BMC within ${cbmc_secs}s; brute-force above is the working check)" ;;
            *)   note FAIL "cbmc atom axioms (symbolic proof)" ;;
        esac
        rc2=0
        timeout "$cbmc_secs" cbmc --bounds-check --pointer-check \
                --unsigned-overflow-check \
                $inc tests/cbmc/xpak_bounds.c >/dev/null 2>&1 || rc2=$?
        case "$rc2" in
            0)   note PASS "cbmc xpak data-bounds (symbolic proof)" ;;
            124) note SKIP "cbmc xpak data-bounds (timeout ${cbmc_secs}s)" ;;
            *)   note FAIL "cbmc xpak data-bounds (symbolic proof)" ;;
        esac
        rc2=0
        timeout "$cbmc_secs" cbmc --bounds-check --pointer-check \
                --unwind 20 --unwinding-assertions \
                $inc tests/cbmc/xpak_copy.c >/dev/null 2>&1 || rc2=$?
        case "$rc2" in
            0)   note PASS "cbmc xpak entry-copy bounds (symbolic proof)" ;;
            124) note SKIP "cbmc xpak entry-copy bounds (timeout ${cbmc_secs}s)" ;;
            *)   note FAIL "cbmc xpak entry-copy bounds (symbolic proof)" ;;
        esac
    else
        note SKIP "cbmc symbolic proof (cbmc not installed)"
    fi
}

restore_default() {
    show "cleanup: restoring a normal default build"
    make clean >>"$QOUT" 2>&1
    ./configure "${RESTORE_FEATURES[@]}" >>"$QOUT" 2>&1 && make -j"$CPU_JOBS" >>"$QOUT" 2>&1
}

# TESTMYCODE_PARALLEL=1: run the selected cehcks in up to 4 isolated copies
# concurrently (tests/r/pN/), via a full separate rsync.
# Each group has its own definition and purpose of course.
parallel_gate_group() {
    case "$1" in
        fuzz|cbmc|cppcheck)                 echo 1 ;;
        asan|integer|tsan|heap)             echo 2 ;;
        gcc|warnings|opt|lto|c23|fanalyzer|static) echo 3 ;;
        clang|tidy|m32|valgrind|flagmatrix) echo 4 ;;
        *)                                  echo 0 ;;
    esac
}

parallel_run() {
    local -a pg1=() pg2=() pg3=() pg4=()
    local g rr=1 prc=0 pj i pbase plogs
    local -a ppids=() pnames=()

    for g in "$@"; do
        case "$(parallel_gate_group "$g")" in
            1) pg1+=("$g") ;;
            2) pg2+=("$g") ;;
            3) pg3+=("$g") ;;
            4) pg4+=("$g") ;;
            *) case "$rr" in
                   1) pg1+=("$g") ;;
                   2) pg2+=("$g") ;;
                   3) pg3+=("$g") ;;
                   4) pg4+=("$g") ;;
               esac
               rr=$((rr % 4 + 1)) ;;
        esac
    done

    plogs="tests/r/logs/$(date +%Y%m%d-%H%M%S)"
    mkdir -p "$plogs"
    ln -sfn "${plogs##*/}" tests/r/logs/last
    exec 9>tests/r/.lock
    if ! flock -n 9; then
        printf 'TESTMYCODE_PARALLEL: another parallel run holds %s\n' \
            "tests/r/.lock" >&2
        return 2
    fi
    pj=$((CPU_JOBS / 4))
    [ "$pj" -lt 1 ] && pj=1
    pbase="${TESTMYCODE_PARALLEL_DIR:-$PWD/tests/r}"
    mkdir -p "$pbase"

    for i in 1 2 3 4; do
        local -n pgrp="pg$i"
        [ "${#pgrp[@]}" -eq 0 ] && continue
        show "parallel$i: ${pgrp[*]} (CPU_JOBS=$pj)"
        rsync -a --delete --exclude=.git --exclude=.docker \
            --exclude='/tests/r' --exclude='tests/*/q-tmp' \
            --exclude=.parallel --exclude='/internal-libs' \
            ./ "$pbase/p$i/"
        (
            cd "$pbase/p$i" || exit 2
            sc=()
            [ "$want_internal" -eq 1 ] && sc=(internal)
            Q_SHORT_TMPDIR=1 TESTMYCODE_LANE=1 TESTMYCODE_PARALLEL=0 CPU_JOBS="$pj" \
                ./testmycode.sh "${sc[@]}" "${pgrp[@]}"
        ) >"$plogs/p$i.log" 2>&1 &
        ppids+=($!)
        pnames+=("$i")
    done

    for i in "${!ppids[@]}"; do
        wait "${ppids[$i]}" || prc=1
    done
    local cdir t
    for i in "${pnames[@]}"; do
        for cdir in "$pbase/p$i"/tests/r/corpus/*/; do
            [ -d "$cdir" ] || continue
            t=${cdir%/}; t=${t##*/}
            mkdir -p "tests/r/corpus/$t"
            cp -n "$cdir"* "tests/r/corpus/$t/" 2>/dev/null
        done
    done
    for i in "${pnames[@]}"; do
        printf '\n\033[1;34m==== parallel%s summary ====\033[0m\n' "$i"
        sed -n '/==== SUMMARY ====/,$p' "$plogs/p$i.log" \
            | sed '1d'
    done
    return "$prc"
}

run_gate() {
    if [ "$HAVE_GCC" -eq 0 ]; then
        case " $GCC_GATES " in
            *" $1 "*) show "check gate $1"; note SKIP "$1 (no gcc on this host)"; return 0 ;;
        esac
    fi
    if [ "$HAVE_CLANG" -eq 0 ]; then
        case " $CLANG_GATES " in
            *" $1 "*) show "check gate $1"; note SKIP "$1 (no clang on this host)"; return 0 ;;
        esac
    fi
    case "$1" in
        gcc)       gcc_gate ;;
        clang)     clang_gate ;;
        opt)       opt_gate ;;
        lto)       lto_gate ;;
        c23)       c23_gate ;;
        asan)      asan_gate ;;
        integer)   integer_gate ;;
        tsan)      tsan_gate ;;
        flagmatrix) flagmatrix_gate ;;
        static)    static_gate ;;
        warnings)  warnings_gate ;;
        cppcheck)  cppcheck_gate ;;
        fanalyzer) fanalyzer_gate ;;
        tidy)      tidy_gate ;;
        heap)      heap_gate ;;
        m32)       m32_gate ;;
        valgrind)  if [ -n "$vg_chroot" ]; then
                       valgrind_chroot_gate "$vg_chroot"
                   else
                       valgrind_gate
                   fi ;;
        fuzz)      fuzz_gate ;;
        cbmc)      cbmc_gate ;;
    esac
}

selected=()
skip_cppcheck=0
vg_chroot=""
vg_expect_dir=0
want_internal=0
for arg in "$@"; do
    if [ "$vg_expect_dir" -eq 1 ]; then
        vg_expect_dir=0
        isgate=0
        for g in "${ALL_GATES[@]}"; do [ "$arg" = "$g" ] && isgate=1; done
        if [ "$isgate" -eq 0 ]; then
            vg_chroot="${arg%/}"
            continue
        fi
    fi
    case "$arg" in
        list)
            for g in "${ALL_GATES[@]}"; do
                tag=""
                for o in "${OPTIONAL_GATES[@]}"; do [ "$g" = "$o" ] && tag="  (optional)"; done
                printf '%s%s\n' "$g" "$tag"
            done
            printf 'internal (modifier: configure the selected check gates --enable-internal-libs; needs src/curl/configure)\n'
            exit 0
            ;;
        --no-cppcheck|--skip-cppcheck)
            skip_cppcheck=1
            ;;
        clean)
            rm -rf tests/r
            printf 'tests/r removed\n'
            exit 0
            ;;
        -h|--help)
            sed -n "2,${HELP_END}p" "$0" | sed 's/^# \{0,1\}//'
            printf '\nDetected CPU threads on this system: %s (current CPU_JOBS: %s)\n' \
                "$([ "$NCPU" -gt 0 ] && printf '%s' "$NCPU" || printf 'unknown')" \
                "$CPU_JOBS"
            jobs_advice
            exit 0
            ;;
        chroot)
            last=""
            [ "${#selected[@]}" -gt 0 ] && last="${selected[${#selected[@]}-1]}"
            if [ "$last" != valgrind ]; then
                printf 'chroot: only valid right after the valgrind check gate\n' >&2
                exit 2
            fi
            vg_chroot="$VG_CHROOT_DEFAULT"
            vg_expect_dir=1
            ;;
        internal)
            want_internal=1
            ;;
        *)
            found=0
            for g in "${ALL_GATES[@]}"; do
                [ "$arg" = "$g" ] && found=1
            done
            if [ "$found" -eq 1 ]; then
                selected+=("$arg")
            else
                printf 'unknown check gate: %s (try: %s)\n' "$arg" "${ALL_GATES[*]}" >&2
                exit 2
            fi
            ;;
    esac
done

if [ "$want_internal" -eq 1 ]; then
    if [ ! -f src/curl/configure ]; then
        printf 'internal: no configure script in src/curl (unpack a curl source tree there)\n' >&2
        exit 2
    fi
    FEATURES+=(--enable-internal-libs)
    show "internal mode: every check configures --enable-internal-libs (static and m32 included)"
fi

[ "${TESTMYCODE_LANE:-0}" = "0" ] && jobs_advice

par_done=0
if [ "${TESTMYCODE_PARALLEL:-0}" != "0" ]; then
    plist=()
    if [ "${#selected[@]}" -eq 0 ]; then
        for g in "${ALL_GATES[@]}"; do
            opt=0
            for o in "${OPTIONAL_GATES[@]}"; do [ "$g" = "$o" ] && opt=1; done
            if [ "$opt" -eq 1 ]; then
                note SKIP "$g (optional; run: ./testmycode.sh $g)"
                continue
            fi
            if [ "$g" = cppcheck ] && [ "$skip_cppcheck" -eq 1 ]; then
                note SKIP "cppcheck (--no-cppcheck)"
                continue
            fi
            plist+=("$g")
        done
    else
        plist=("${selected[@]}")
    fi
    if [ "${#plist[@]}" -gt 1 ]; then
        show "TESTMYCODE_PARALLEL: ${#plist[@]} test gates in up to 4 isolated source-tree copies"
        parallel_run "${plist[@]}" || rc=1
        par_done=1
    fi
fi

if [ "$par_done" -eq 0 ]; then
if [ "${TESTMYCODE_LANE:-0}" = "0" ]; then
    slogs="tests/r/logs/$(date +%Y%m%d-%H%M%S)"
    mkdir -p "$slogs"
    ln -sfn "${slogs##*/}" tests/r/logs/last
    exec > >(tee "$slogs/serial.log") 2>&1
fi
if [ "${#selected[@]}" -eq 0 ]; then
    for g in "${ALL_GATES[@]}"; do
        opt=0
        for o in "${OPTIONAL_GATES[@]}"; do [ "$g" = "$o" ] && opt=1; done
        if [ "$opt" -eq 1 ]; then
            show "check gate $g: optional (not in the default pass)"
            note SKIP "$g (optional; run: ./testmycode.sh $g)"
            continue
        fi
        if [ "$g" = cppcheck ] && [ "$skip_cppcheck" -eq 1 ]; then
            show "check gate cppcheck: static analysis"
            note SKIP "cppcheck (--no-cppcheck)"
            continue
        fi
        run_gate "$g"
    done
else
    for g in "${selected[@]}"; do
        run_gate "$g"
    done
fi

restore_default
fi

show "SUMMARY"
for line in "${summary[@]}"; do
    printf '  %s\n' "$line"
done
if [ "$rc" -eq 0 ]; then
    printf '\n\033[1;32mAll (check) gates passed. Safe to open the pull request.\033[0m\n'
else
    printf '\n\033[1;31mOne or more check gates failed. Fix before pushing.\033[0m\n'
fi
exit "$rc"
