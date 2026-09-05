#!/bin/bash
set -eo pipefail

cd "$(dirname "$0")/../.."

: "${SOAKSECS:=600}"
: "${FORKS:=6}"
: "${AFL_DRIVER:=/usr/lib64/afl/libAFLDriver.a}"
read -ra TARGETS <<< "${FUZZ_TARGETS:-atom dep contents packages gpkg_manifest gpkg_structure envd binpath binrepos moves needed preserved usedep useflags xpak hash mfline elfneeded dcx}"

CC=afl-gcc-fast AFL_USE_ASAN=1 SANFLAGS='' CFLAGS='-O1 -g' COV_FLAGS='' \
    LIB_FUZZING_ENGINE="$AFL_DRIVER" tests/fuzz/build.sh

export AFL_SKIP_CPUFREQ=1 AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1
export AFL_NO_UI=1 AFL_AUTORESUME=1

rc=0
for t in "${TARGETS[@]}"; do
    out="tests/r/afl/${t}"
    mkdir -p "$out"
    indir="tests/fuzz/seeds/${t}"
    [ -n "$(ls -A "tests/r/corpus/${t}" 2>/dev/null)" ] && indir="tests/r/corpus/${t}"
    dictarg=()
    [ -f "tests/fuzz/dict/${t}.dict" ] && dictarg=(-x "tests/fuzz/dict/${t}.dict")
    printf '\n==== afl soak fuzz_%s: %s instances for %ss ====\n' "$t" "$FORKS" "$SOAKSECS"
    pids=()
    for i in $(seq 1 "$FORKS"); do
        if [ "$i" -eq 1 ]; then role=(-M main); else role=(-S "sec$i"); fi
        afl-fuzz -m none -V "$SOAKSECS" "${dictarg[@]}" \
            -i "$indir" -o "$out" "${role[@]}" -- "tests/fuzz/.bin/fuzz_${t}" \
            >"$out/run-$i.log" 2>&1 &
        pids+=($!)
    done
    wait "${pids[@]}" || :
    crashes=$(find "$out" -path '*/crashes/id:*' 2>/dev/null | wc -l)
    if [ "$crashes" -gt 0 ]; then
        rc=1
        printf 'fuzz_%s: %s afl crash(es) in %s/*/crashes/\n' "$t" "$crashes" "$out" >&2
    fi
done
exit "$rc"