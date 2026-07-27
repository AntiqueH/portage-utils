#!/bin/bash
#
# testmycode.sh
#
# Run this from the portage-utils source root BEFORE opening a pull request.
# It runs the full local sanity suite from a clean tree at every stage and
# exits non-zero if anything regresses. The stages, and why each exists:
#
#   1. GCC warnings+errors gate (-O2, --enable-werror): a clean build where
#      every compiler warning in our own code becomes a hard error. -Werror
#      is scoped through CWFLAGS to portage-utils sources + libq only, so the
#      vendored gnulib and curl trees (which warn on their own terms) never
#      trip it. -O2 is used because many diagnostics only fire with the
#      optimizer on.
#   2. Clang warnings+errors gate (-O2, --enable-werror): the same gate built
#      with clang, which reports a different, wider set of warnings than gcc.
#   3. Optimization gate (-O3, --enable-werror): a clean -O3 build to surface
#      optimization-only diagnostics such as -Wmaybe-uninitialized and
#      -Wstringop-/-Wformat-truncation that do not appear at lower levels.
#   4. Sanitizer run (ASan + UBSan): build with
#      -fsanitize=address,undefined -fno-sanitize-recover=all and then run
#      "make check", so the test suite exercises the code under the
#      use-after-free, heap-overflow, leak and undefined-behavior detectors.
#      This is the regime that has caught the real memory bugs in this tree.
#   5. cppcheck static analysis (skipped if cppcheck is not installed): a
#      static pass over our sources only, vendored trees excluded.
#
# Gates 1 to 3 also apply the Gentoo "Modern C porting" flag set as errors
# (https://wiki.gentoo.org/wiki/Modern_C_porting):
# -Werror=implicit-function-declaration, -Werror=implicit-int,
# -Werror=int-conversion, -Werror=incompatible-pointer-types and
# -Werror=strict-prototypes. These are the constructs that GCC 14 and recent
# Clang promoted to hard errors by default; enforcing them here catches code
# that will fail to build on new toolchains even when your local compiler is
# older, while the codebase itself stays C99. For a deeper interprocedural
# pass, run GCC's static analyzer over a single file directly, for example:
#   gcc -fanalyzer -fsyntax-only -std=c99 -DHAVE_CONFIG_H \
#       -I. -I libq -I autotools/gnulib -I src/curl/include \
#       $(pkg-config --cflags gpgme libarchive) qmerge.c
#
# The tree is left in a normal default build afterwards. Override the
# parallelism with JOBS=N and the feature set with FEATURES="...". A green
# run of all gates is the bar for pushing a pull request.
#
set -u

JOBS="${JOBS:-30}"
read -ra FEATURES <<< "${FEATURES:---enable-qmanifest --enable-gpkg --enable-gtree}"
SAN_CFLAGS="-O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined -fno-sanitize-recover=all"
SAN_LDFLAGS="-fsanitize=address,undefined"
MODERN_C="-Werror=implicit-function-declaration -Werror=implicit-int -Werror=int-conversion -Werror=incompatible-pointer-types -Werror=strict-prototypes"

run_cppcheck=1
for arg in "$@"; do
    case "$arg" in
        --no-cppcheck|--skip-cppcheck) run_cppcheck=0 ;;
        *) printf 'unknown argument: %s\n' "$arg" >&2; exit 2 ;;
    esac
done

summary=()
rc=0

hr() {
    printf '\n\033[1;34m==== %s ====\033[0m\n' "$*"
}

note() {
    summary+=("$(printf '%-5s %s' "$1" "$2")")
    [ "$1" = FAIL ] && rc=1
    return 0
}

gcc_gate() {
    hr "1/5 GCC warnings+errors+modern-C gate (-O2 -Werror)"
    make clean >/dev/null 2>&1
    if ./configure --enable-werror "${FEATURES[@]}" CFLAGS="-O2 -g $MODERN_C" >/dev/null 2>&1 \
            && make -j"$JOBS"; then
        note PASS "gcc -Werror -O2"
    else
        note FAIL "gcc -Werror -O2"
    fi
}

clang_gate() {
    hr "2/5 Clang warnings+errors+modern-C gate (-O2 -Werror)"
    make clean >/dev/null 2>&1
    if CC=clang ./configure --enable-werror "${FEATURES[@]}" CFLAGS="-O2 -g $MODERN_C" >/dev/null 2>&1 \
            && make -j"$JOBS" CC=clang; then
        note PASS "clang -Werror -O2"
    else
        note FAIL "clang -Werror -O2"
    fi
}

opt_gate() {
    hr "3/5 Optimization + modern-C gate (-O3 -Werror)"
    make clean >/dev/null 2>&1
    if ./configure --enable-werror "${FEATURES[@]}" CFLAGS="-O3 -g $MODERN_C" >/dev/null 2>&1 \
            && make -j"$JOBS"; then
        note PASS "gcc -Werror -O3"
    else
        note FAIL "gcc -Werror -O3"
    fi
}

sanitizer_run() {
    hr "4/5 ASan+UBSan build and test suite (make check)"
    make clean >/dev/null 2>&1
    if ./configure "${FEATURES[@]}" CFLAGS="$SAN_CFLAGS" LDFLAGS="$SAN_LDFLAGS" >/dev/null 2>&1 \
            && make -j"$JOBS" \
            && ASAN_OPTIONS="detect_leaks=1:abort_on_error=1:strict_string_checks=1" \
               UBSAN_OPTIONS="print_stacktrace=1:halt_on_error=1" \
               make check; then
        note PASS "asan+ubsan make check"
    else
        note FAIL "asan+ubsan make check"
    fi
}

cppcheck_run() {
    hr "5/5 cppcheck static analysis"
    if ! command -v cppcheck >/dev/null 2>&1; then
        note SKIP "cppcheck (not installed)"
        return 0
    fi
    if cppcheck --std=c99 --quiet \
            --inline-suppr --error-exitcode=2 \
            --suppressions-list=.cppcheck-suppressions \
            --suppress=missingIncludeSystem --suppress=unmatchedSuppression \
            -i src/curl -i autotools/gnulib -I libq -I . ./*.c libq/*.c; then
        note PASS "cppcheck"
    else
        note FAIL "cppcheck"
    fi
}

restore_default() {
    hr "cleanup: restoring a normal default build"
    make clean >/dev/null 2>&1
    ./configure "${FEATURES[@]}" >/dev/null 2>&1 && make -j"$JOBS" >/dev/null 2>&1
}

gcc_gate
clang_gate
opt_gate
sanitizer_run
if [ "$run_cppcheck" -eq 1 ]; then
    cppcheck_run
else
    hr "5/5 cppcheck static analysis"
    note SKIP "cppcheck (--no-cppcheck)"
fi
restore_default

hr "SUMMARY"
for line in "${summary[@]}"; do
    printf '  %s\n' "$line"
done
if [ "$rc" -eq 0 ]; then
    printf '\n\033[1;32mAll gates passed. Safe to open the pull request.\033[0m\n'
else
    printf '\n\033[1;31mOne or more gates failed. Fix before pushing.\033[0m\n'
fi
exit "$rc"
