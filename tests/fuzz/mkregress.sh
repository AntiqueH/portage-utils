#!/bin/sh
# Run before the fuzz gate
# and regress.sh. the generated files are gitignored (gen-*).
set -e

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/seeds

# libq/xpak.c tbz2-footer signed-int overflow (xpak.c:160).
mkdir -p "$here/xpak"
printf '\0\0\0\0\0\0\0\0\177\377\377\377STOP' > "$here/xpak/gen-int-overflow-footer"

# libq/envd.c ld.so.conf include glob DoS (multi-wildcard filesystem crawl).
mkdir -p "$here/envd"
printf 'include //*//*//*//*//*//*\n' > "$here/envd/gen-glob-dos"
