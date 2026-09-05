#!/bin/bash
set -eo pipefail

cd "$(dirname "$0")/../.."

for d in /usr/lib/llvm/*/bin; do [ -x "$d/llvm-cov" ] && PATH="$d:$PATH"; done
export PATH
read -ra TARGETS <<< "${FUZZ_TARGETS:-atom dep contents packages gpkg_manifest gpkg_structure envd binpath binrepos moves needed preserved usedep useflags xpak hash mfline elfneeded dcx}"

declare -A SRC=(
    [atom]=libq/atom.c
    [dep]=libq/dep.c
    [contents]=libq/contents.c
    [packages]=libq/tree.c
    [gpkg_manifest]=libq/gpkg.c
    [gpkg_structure]=libq/gpkg.c
    [envd]=libq/envd.c
    [binpath]=libq/binpath.c
    [binrepos]=libq/binrepos.c
    [moves]=libq/moves.c
    [usedep]=libq/usedep.c
    [useflags]=libq/useflags.c
    [xpak]=libq/xpak.c
    [hash]=libq/hash.c
    [needed]=libq/linkage.c
    [preserved]=libq/preserved.c
    [mfline]=libq/mfline.c
    [elfneeded]=libq/elfneeded.c
)

COV=tests/r/coverage
rm -rf "$COV"; mkdir -p "$COV/bin"

CC=clang \
    SANFLAGS="-fprofile-instr-generate -fcoverage-mapping" \
    CFLAGS="-O1 -g -fprofile-instr-generate -fcoverage-mapping" \
    COV_FLAGS="-fsanitize=fuzzer-no-link" \
    LIB_FUZZING_ENGINE="-fsanitize=fuzzer -fprofile-instr-generate -fcoverage-mapping" \
    OUT="$COV/bin" \
    tests/fuzz/build.sh >/dev/null

printf '\n%-16s %-14s %s\n' "target" "parser" "line coverage"
for t in "${TARGETS[@]}"; do
    ins=()
    [ -d "tests/r/corpus/$t" ] && ins+=("tests/r/corpus/$t")
    [ -d "tests/fuzz/seeds/$t" ]   && ins+=("tests/fuzz/seeds/$t")
    LLVM_PROFILE_FILE="$COV/$t.profraw" ASAN_OPTIONS=detect_leaks=0 \
        "$COV/bin/fuzz_$t" -runs=0 "${ins[@]}" >/dev/null 2>&1 || :
    llvm-profdata merge -sparse "$COV/$t.profraw" -o "$COV/$t.profdata" 2>/dev/null
    line=$(llvm-cov report "$COV/bin/fuzz_$t" -instr-profile="$COV/$t.profdata" \
        "${SRC[$t]}" 2>/dev/null | awk -v f="${SRC[$t]##*/}" '$1 ~ f {print $10}')
    printf '%-16s %-14s %s\n' "$t" "${SRC[$t]##*/}" "${line:-n/a}"
    llvm-cov show "$COV/bin/fuzz_$t" -instr-profile="$COV/$t.profdata" \
        "${SRC[$t]}" -format=html -output-dir="$COV/html_$t" >/dev/null 2>&1 || :
done
echo
echo "per-line HTML: $COV/html_<target>/index.html"
