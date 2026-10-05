#!/bin/bash
# Build a fuzz target that compiles main.c and qmerge.c,
# fuzz_dcx, or the target named as the first argument (qmhelpers, resolve)
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
T=${1:-dcx}
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
	"tests/fuzz/fuzz_$T.c" $qsrc $qlibs $libs -o "$OUT/fuzz_$T"
echo "built $OUT/fuzz_$T"