dnl Copyright 2026-     Gentoo Authors
dnl Distributed under the terms of the GNU General Public License v2
dnl
dnl Copyright 2026-     Jaeger H.       - <antiq.hofer@gmail.com>

AC_DEFUN([PT_INTERNAL_LIBS], [
AC_ARG_ENABLE([internal-libs],
  [AS_HELP_STRING([--enable-internal-libs],
    [build the libraries found under src/ (currently src/curl) into q instead of linking the system ones; a src/<lib> without a configure script we skip])],
  [], [enable_internal_libs=no])
AC_ARG_VAR([INTERNAL_CFLAGS], [C compiler flags for the internal libraries under src/ (default: CFLAGS without -Werror)])
AC_ARG_VAR([INTERNAL_CPPFLAGS], [C preprocessor flags for the internal libraries under src/ (default: CPPFLAGS)])
AC_ARG_VAR([INTERNAL_LDFLAGS], [linker flags for the internal libraries under src/ (default: LDFLAGS)])
])

AC_DEFUN([PT_INTERNAL_CURL], [
AC_REQUIRE([PT_INTERNAL_LIBS])
pt_curl_src="$srcdir/src/curl"
pt_curl_build="internal-libs/curl"
pt_internal_curl=no

AS_IF([test "x${enable_internal_libs}" = "xyes"],
  [AC_MSG_CHECKING([for a curl source tree with configure options in src/curl])
   AS_IF([test -f "$pt_curl_src/configure"],
     [AS_IF([test -f "$pt_curl_src/config.status"],
        [AC_MSG_RESULT([configured in place])
         AC_MSG_WARN([src/curl was configured in place and cannot be built out of tree; internal curl skipped, using the system libcurl])],
        [AC_MSG_RESULT([yes])
         pt_internal_curl=yes])],
     [test -f "$pt_curl_src/configure.ac"],
     [AC_MSG_RESULT([configure.ac only])
      AC_MSG_WARN([src/curl has no configure script; internal curl skipped, using the system libcurl])],
     [AC_MSG_RESULT([no])
      AC_MSG_WARN([no curl source tree in src/curl; internal curl skipped, using the system libcurl])])])

AS_IF([test "x${pt_internal_curl}" = "xyes"],
  [pt_curl_vernum=`sed -n 's/^#define LIBCURL_VERSION_NUM *0x\(......\).*/\1/p' "$pt_curl_src/include/curl/curlver.h" 2>/dev/null`
   AS_IF([test -z "$pt_curl_vernum"],
     [AC_MSG_FAILURE([cannot read LIBCURL_VERSION_NUM from src/curl/include/curl/curlver.h])])
   AS_IF([test "`expr "$pt_curl_vernum" \< 075500`" = 1],
     [AC_MSG_FAILURE([the curl in src/curl is older than 7.85.0 (LIBCURL_VERSION_NUM 0x$pt_curl_vernum); qmerge needs CURLOPT_REDIR_PROTOCOLS_STR])])

   pt_curl_minimal="
     --disable-shared --enable-static --with-pic
     --with-openssl --with-zlib
     --without-brotli --without-zstd --without-libpsl --without-libidn2
     --without-nghttp2 --without-nghttp3 --without-ngtcp2 --without-quiche
     --without-libssh2 --without-libssh --without-librtmp
     --without-gssapi --without-libgsasl
     --disable-ftp --disable-file --disable-ldap --disable-ldaps
     --disable-rtsp --disable-dict --disable-telnet --disable-tftp
     --disable-pop3 --disable-imap --disable-smb --disable-smtp
     --disable-gopher --disable-mqtt --disable-ipfs --disable-websockets
     --disable-manual --disable-docs --disable-libcurl-option
     --disable-get-easy-options --disable-ares --disable-sspi
     --disable-ntlm --disable-tls-srp --disable-doh --disable-ech
     --disable-httpsrr --disable-alt-svc --disable-hsts
     --disable-headers-api --disable-mime --disable-form-api
     --disable-cookies --disable-netrc --disable-aws --disable-bindlocal
     --disable-dnsshuffle --disable-unix-sockets --disable-socketpair
     --disable-sha512-256 --disable-negotiate-auth
     --disable-kerberos-auth --disable-bearer-auth
   "
   pt_curl_help=`$SHELL "$pt_curl_src/configure" --help 2>/dev/null`
   pt_curl_args=
   pt_curl_unknown=
   for pt_opt in $pt_curl_minimal; do
     pt_name=`echo "$pt_opt" | sed 's/^--without-//;s/^--with-//;s/^--disable-//;s/^--enable-//'`
     AS_CASE(["$pt_curl_help"],
       [*"--enable-$pt_name"*|*"--disable-$pt_name"*|*"--with-$pt_name"*|*"--without-$pt_name"*],
       [pt_curl_args="$pt_curl_args $pt_opt"],
       [pt_curl_unknown="$pt_curl_unknown $pt_opt"])
   done
   AS_IF([test -n "$pt_curl_unknown"],
     [AC_MSG_NOTICE([internal curl: options unknown to this curl version, skipped:$pt_curl_unknown])])

   AS_IF([test "${INTERNAL_CFLAGS+set}" = set],
     [pt_curl_cflags=$INTERNAL_CFLAGS],
     [pt_curl_cflags=
      for pt_f in ${pt_user_CFLAGS-$CFLAGS}; do
        AS_CASE([$pt_f],
          [-Werror|-Werror=*], [],
          [pt_curl_cflags="$pt_curl_cflags $pt_f"])
      done])
   pt_curl_cppflags=${INTERNAL_CPPFLAGS-$CPPFLAGS}
   pt_curl_ldflags=${INTERNAL_LDFLAGS-$LDFLAGS}

   pt_curl_hostargs=
   AS_IF([test -n "$host_alias"], [pt_curl_hostargs="$pt_curl_hostargs --host=$host_alias"])
   AS_IF([test -n "$build_alias"], [pt_curl_hostargs="$pt_curl_hostargs --build=$build_alias"])
   AS_CASE(["$PKG_CONFIG"],
     [*" "*], [pt_curl_pkgconfig=],
     [pt_curl_pkgconfig="$PKG_CONFIG"])

   AS_MKDIR_P(["$pt_curl_build"])
   pt_curl_abssrc=`cd "$pt_curl_src" && pwd`
   AC_MSG_NOTICE([=== configuring internal curl in $pt_curl_build])
   (cd "$pt_curl_build" || exit 1
    AS_IF([test -n "$pt_curl_pkgconfig"],
      [PKG_CONFIG=$pt_curl_pkgconfig; export PKG_CONFIG],
      [unset PKG_CONFIG])
    CONFIG_SHELL=$SHELL; export CONFIG_SHELL
    exec $SHELL "$pt_curl_abssrc/configure" --disable-option-checking \
      --srcdir="$pt_curl_abssrc" --cache-file=/dev/null \
      $pt_curl_hostargs $pt_curl_args \
      CC="$CC" CFLAGS="$pt_curl_cflags" CPPFLAGS="$pt_curl_cppflags" LDFLAGS="$pt_curl_ldflags") \
     || AC_MSG_FAILURE([internal curl: configure failed, see $pt_curl_build/config.log])
   AC_MSG_NOTICE([=== internal curl configured])

   pt_curl_pc="$pt_curl_build/libcurl.pc"
   AS_IF([test -f "$pt_curl_pc" && test -f "$pt_curl_build/lib/Makefile"], [],
     [AC_MSG_FAILURE([internal curl: $pt_curl_pc or $pt_curl_build/lib/Makefile was not generated])])
   pt_curl_version=`sed -n 's/^Version: *//p' "$pt_curl_pc"`
   INTERNAL_CURL_LIBS=`sed -n 's/^Libs\.private: *//p' "$pt_curl_pc"`
   pt_curl_requires=`sed -n 's/^Requires\.private: *//p' "$pt_curl_pc" | tr ',' ' '`
   AS_IF([test -n "$pt_curl_requires"],
     [INTERNAL_CURL_LIBS="$INTERNAL_CURL_LIBS `$PKG_CONFIG --libs $pt_curl_requires 2>/dev/null`"])
   AS_IF([test "x${enable_static}" = "xyes"],
     [INTERNAL_CURL_LIBS="$INTERNAL_CURL_LIBS `$PKG_CONFIG --libs openssl zlib 2>/dev/null`"])
   AC_SUBST([INTERNAL_CURL_LIBS])
   AC_MSG_NOTICE([internal curl $pt_curl_version: HTTP(S) only, OpenSSL, zlib; linked into q as libcurl.a])],
  [PKG_CHECK_MODULES([LIBCURL], [libcurl >= 7.85.0],
     [AC_MSG_NOTICE([using system libcurl])],
     [AC_MSG_FAILURE([libcurl.pc (7.85.0 or newer) not found; install libcurl, or put a curl source tree in src/curl and pass --enable-internal-libs])])])

AM_CONDITIONAL([INTERNAL_CURL], [test "x${pt_internal_curl}" = "xyes"])
])