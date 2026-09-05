#!/bin/bash
set -eo pipefail

cd "$(dirname "$0")/../.."

: "${CC:=clang}"
: "${SANFLAGS=-fsanitize=address,undefined -fno-sanitize-recover=all}"
: "${CFLAGS:=-O1 -g ${SANFLAGS}}"
: "${COV_FLAGS=-fsanitize=fuzzer-no-link}"
: "${LIB_FUZZING_ENGINE:=-fsanitize=fuzzer}"
: "${OUT:=tests/fuzz/.bin}"
: "${JOBS:=$(nproc)}"
read -ra TARGETS <<< "${FUZZ_TARGETS:-atom dep contents packages gpkg_manifest gpkg_structure envd binpath binrepos moves needed preserved usedep useflags xpak hash mfline elfneeded dcx}"

gpgme_cflags=$(pkg-config --cflags gpgme 2>/dev/null || gpgme-config --cflags 2>/dev/null || :)

make clean >/dev/null 2>&1
CC="$CC" ./configure --enable-qmanifest --enable-gpkg --enable-gtree --disable-openmp \
    CFLAGS="${CFLAGS} ${COV_FLAGS}" LDFLAGS="${SANFLAGS}" >/dev/null
make -j"$JOBS" CC="$CC" >/dev/null

mkdir -p "$OUT"
inc="-DHAVE_CONFIG_H -I. -Ilibq -Iautotools/gnulib ${gpgme_cflags}"
for t in "${TARGETS[@]}"; do
    if [ "$t" = dcx ]; then
        CC="$CC" FUZZ_CFLAGS="${CFLAGS} ${LIB_FUZZING_ENGINE}" OUT="$OUT" \
            tests/fuzz/build-dcx.sh
        continue
    fi
    "$CC" ${CFLAGS} ${LIB_FUZZING_ENGINE} ${inc} \
        "tests/fuzz/fuzz_${t}.c" libq/libq.a autotools/gnulib/libgnu.a \
        -larchive -lz -lb2 -o "${OUT}/fuzz_${t}"
    echo "built ${OUT}/fuzz_${t}"
done