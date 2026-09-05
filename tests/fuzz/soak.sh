#!/bin/bash
set -eo pipefail

cd "$(dirname "$0")/../.."

: "${SOAKSECS:=600}"
: "${FORKS:=6}"
read -ra TARGETS <<< "${FUZZ_TARGETS:-atom dep contents packages gpkg_manifest gpkg_structure envd binpath binrepos moves needed preserved usedep useflags xpak hash mfline elfneeded dcx}"

tests/fuzz/build.sh

rc=0
for t in "${TARGETS[@]}"; do
    mkdir -p "tests/r/corpus/${t}"
    dict=()
    [ -f "tests/fuzz/dict/${t}.dict" ] && dict=("-dict=tests/fuzz/dict/${t}.dict")
    seeds=()
    [ -d "tests/fuzz/seeds/${t}" ] && seeds+=("tests/fuzz/seeds/${t}")
    [ -d "tests/fuzz/regressions/${t}" ] && seeds+=("tests/fuzz/regressions/${t}")
    printf '\n==== soak fuzz_%s: %s forks for %ss ====\n' "$t" "$FORKS" "$SOAKSECS"
    if ! ASAN_OPTIONS=detect_leaks=${LEAK:-0} "tests/fuzz/.bin/fuzz_${t}" \
            -fork="$FORKS" -max_total_time="$SOAKSECS" -use_value_profile=1 \
            -print_funcs=0 \
            -rss_limit_mb=4096 -timeout=25 "${dict[@]}" \
            -artifact_prefix="tests/r/artifacts/${t}-" \
            "tests/r/corpus/${t}" "${seeds[@]}"; then
        rc=1
        printf 'fuzz_%s: FAILURE, reproducer(s) in tests/r/artifacts/%s-*\n' \
            "$t" "$t" >&2
    fi
done
exit "$rc"
