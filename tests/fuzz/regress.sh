#!/bin/bash
set -eo pipefail

cd "$(dirname "$0")/../.."

read -ra TARGETS <<< "${FUZZ_TARGETS:-atom dep contents packages gpkg_manifest gpkg_structure envd binpath binrepos moves needed preserved usedep useflags xpak hash mfline elfneeded dcx}"

sh tests/fuzz/mkregress.sh

[ -x tests/fuzz/.bin/fuzz_atom ] || tests/fuzz/build.sh

rc=0
for t in "${TARGETS[@]}"; do
    mapfile -t inputs < <(find "tests/fuzz/seeds/${t}" "tests/fuzz/regressions/${t}" \
        -type f 2>/dev/null)
    [ "${#inputs[@]}" -eq 0 ] && continue
    if ASAN_OPTIONS=detect_leaks=0 "tests/fuzz/.bin/fuzz_${t}" "${inputs[@]}" \
            >/dev/null 2>&1; then
        printf 'regress fuzz_%-14s OK (%d inputs)\n' "$t" "${#inputs[@]}"
    else
        printf 'regress fuzz_%-14s FAILED\n' "$t" >&2
        rc=1
    fi
done
exit "$rc"