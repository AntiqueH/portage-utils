#!/bin/bash
# Build the fuzz_dcx target
# Takes the source list, preprocessor flags and libraries from the generated
# Makefile so it follows configure (vendored curl, gpgme, libarchive).
#
#   CC          compiler (clang)
#   FUZZ_CFLAGS sanitizer/engine flags, e.g. -fsanitize=fuzzer,address,undefined -O1 -g
#   OUT         output directory (tests/fuzz/.bin)
set -eo pipefail
cd "$(dirname "$0")/../.."
: "${CC:=clang}"
: "${FUZZ_CFLAGS:=-O1 -g -fsanitize=fuzzer,address,undefined}"
: "${OUT:=tests/fuzz/.bin}"
[ -f Makefile ] || { echo "build-dcx.sh: run ./configure first" >&2; exit 1; }
mkvar() {
	make -s -f Makefile -f - __q_print "__Q_VAR=$1" <<'EOF'
__q_print:
	@echo $($(__Q_VAR))
EOF
}
qsrc=$(mkvar q_SOURCES | tr ' ' '\n' | grep -v '^main\.c$\|^qmerge\.c$' | tr '\n' ' ')
qcpp=$(mkvar q_CPPFLAGS)
qlibs=$(mkvar q_LDADD)
libs=$(mkvar LIBS)
mkdir -p "$OUT"
# shellcheck disable=SC2086
"$CC" $FUZZ_CFLAGS -DHAVE_CONFIG_H -I. $qcpp \
	tests/fuzz/fuzz_dcx.c $qsrc $qlibs $libs -o "$OUT/fuzz_dcx"
echo "built $OUT/fuzz_dcx"