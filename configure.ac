# Copyright 2011-2026 Gentoo Authors
# Distributed under the terms of the GNU General Public License v2
#
# Copyright 2011-2014 Mike Frysinger  - <vapier@gentoo.org>
# Copyright 2011-     Fabian Groffen  - <grobian@gentoo.org>

AC_PREREQ([2.72])
AC_INIT([portage-utils],[git])
AM_INIT_AUTOMAKE([1.11 dist-xz foreign no-dist-gzip silent-rules -Wall])
AM_SILENT_RULES([yes]) # AM_INIT_AUTOMAKE([silent-rules]) is broken atm
AM_MAINTAINER_MODE([enable])
AC_CONFIG_HEADERS([config.h])
AC_CONFIG_MACRO_DIR([autotools/m4])

AC_PROG_CC
AC_USE_SYSTEM_EXTENSIONS

dnl the codebase must stay buildable as ISO C99 so it remains widely
dnl adoptable (older GCC, and non-GNU compilers alike): force -std=c99
dnl so any C11+ construct or GNU language extension is rejected at
dnl compile time. POSIX/GNU *APIs* stay available through
dnl AC_USE_SYSTEM_EXTENSIONS above (_GNU_SOURCE et al override
dnl strict-ANSI header checks; it must expand before the first compile
dnl test, hence directly after AC_PROG_CC). This block sits right
dnl behind them so all subsequent feature tests (gnulib in particular)
dnl probe the compiler at the same language level. A -std= supplied
dnl in CFLAGS wins.
pt_user_CFLAGS=$CFLAGS
case "$CFLAGS" in
*-std=*)
	AC_MSG_NOTICE([not forcing -std=c99, CFLAGS already selects a standard])
	;;
*)
	AC_MSG_CHECKING([whether $CC accepts -std=c99])
	pt_save_CFLAGS=$CFLAGS
	CFLAGS="$CFLAGS -std=c99"
	AC_COMPILE_IFELSE([AC_LANG_PROGRAM([], [])],
		[AC_MSG_RESULT([yes])],
		[AC_MSG_RESULT([no])
		 CFLAGS=$pt_save_CFLAGS])
	;;
esac
AC_OPENMP
AM_PROG_CC_C_O

gl_EARLY
gl_INIT

AM_PROG_AR
AC_PROG_LN_S

headers='#ifdef HAVE_STDDEF_H
#include <stddef.h>
#endif
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
'
AC_CHECK_HEADERS([stddef.h unistd.h])
AX_COMPILE_CHECK_SIZEOF([size_t],[${headers}])

AC_CHECK_FUNCS_ONCE(m4_flatten([
	   fmemopen
	   scandirat
]))

AC_CHECK_SENDFILE

AC_ARG_WITH([eprefix], [AS_HELP_STRING([--with-eprefix], [path for Gentoo/Prefix project])])
# ensure eprefix ends with a slash, since the code base expects that
case "$with_eprefix" in
	*/) with_eprefix="$with_eprefix" ;;
	*)  with_eprefix="${with_eprefix}/" ;;
esac
AC_DEFINE_UNQUOTED([CONFIG_EPREFIX], ["$with_eprefix"],
				   [Gentoo Prefix offset path])
AC_SUBST([CONFIG_EPREFIX], ["$with_eprefix"])

AC_ARG_ENABLE([qmanifest], [AS_HELP_STRING([--enable-qmanifest],
			  [support qmanifest applet])])

AC_ARG_ENABLE([gpkg],
              [AS_HELP_STRING([--enable-gpkg],
                              [support GLEP-78 gpkg packages])])
AC_ARG_ENABLE([gtree],
              [AS_HELP_STRING([--enable-gtree],
                              [support gtree cache])])
AC_ARG_ENABLE([gpg],
              [AS_HELP_STRING([--disable-gpg],
                              [do not use gpgme; gpkg installs without OpenPGP signature verification])])

AC_ARG_ENABLE([static],
              [AS_HELP_STRING([--enable-static],
                              [link q statically; requires static (.a) libraries for the whole dependency closure])])
PKG_PROG_PKG_CONFIG
AS_IF([test "x${enable_static}" = "xyes"],
      [PKG_CONFIG="$PKG_CONFIG --static"
       AC_DEFINE([Q_STATIC_BUILD], [1],
                 [Define when q is being linked statically])
       AC_MSG_NOTICE([static build: pkg-config queried with --static; the whole dependency chainstuff must provide static (.a) libraries])])


# always check libb2, gpgme and libarchive
PKG_CHECK_MODULES([LIBBL2], [libb2],
                  [
                    AC_DEFINE([HAVE_BLAKE2B], [1], [Define if you have blake2b])
                    LIBBL2="yes"
                  ],
                  [
                    AS_IF([test "x${enable_qmanifest}" = "xyes"],
                          [
                            AC_MSG_FAILURE([--enable-qmanifest was given, but libb2.pc could not be found])
                          ])
                    LIBBL2="no: missing dependencies"
                    enable_qmanifest=no
                  ])

AS_IF([test "x${enable_gpg}" = "xno"],
      [
        AS_IF([test "x${enable_qmanifest}" = "xyes"],
              [AC_MSG_FAILURE([--enable-qmanifest requires gpgme and cannot be used with --disable-gpg])])
        AS_IF([test "x${enable_gtree}" = "xyes"],
              [AC_MSG_FAILURE([--enable-gtree requires gpgme and cannot be used with --disable-gpg])])
        GPGME="no: disabled by --disable-gpg"
        enable_qmanifest=no
        enable_gtree=no
      ],
      [
PKG_CHECK_MODULES([GPGME], [gpgme],
                  [
                    AC_DEFINE([HAVE_GPGME], [1], [Define if you have gpgme])
                    GPGME="yes"
                  ],
                  [
                    AS_IF([test "x${enable_qmanifest}" = "xyes"],
                          [
                            AC_MSG_FAILURE([--enable-qmanifest was given, but gpgme.pc could not be found])
                          ])
                    AS_IF([test "x${enable_gtree}" = "xyes"],
                          [
                            AC_MSG_FAILURE([--enable-gtree was given, but gpgme.pc could not be found])
                          ])
                    GPGME="no: missing dependencies"
                    enable_qmanifest=no
                    enable_gtree=no
                  ])
      ])

dnl libcurl: the system one by default; --enable-internal-libs builds the
dnl curl source tree found in src/curl into q instead (autotools/m4/internal-libs.m4);
dnl --disable-curl leaves the built-in fetcher out, downloads then run
dnl through QFETCHCOMMAND (wget and the like)
AC_ARG_ENABLE([curl],
  [AS_HELP_STRING([--disable-curl],
    [build without libcurl; package and index downloads then need QFETCHCOMMAND (wget for instance)])],
  [enable_curl=$enableval], [enable_curl=yes])
PT_INTERNAL_LIBS
AS_IF([test "x${enable_curl}" != "xno"],
  [PT_INTERNAL_CURL
   AC_DEFINE([HAVE_LIBCURL], [1], [Define if the built-in libcurl fetcher is compiled in])
   do_curl=yes],
  [AC_MSG_NOTICE([libcurl disabled, package and index downloads need QFETCHCOMMAND])
   pt_internal_curl=no
   do_curl=])
AM_CONDITIONAL([INTERNAL_CURL], [test "x${pt_internal_curl}" = "xyes"])

PKG_CHECK_MODULES([LIBARCHIVE], [libarchive],
                  [
                    AC_DEFINE([HAVE_LIBARCHIVE], [1], [Define if you have libarchive])
                    LIBARCHIVE="yes"
                    save_LIBS="$LIBS"
                    LIBS="$LIBS $LIBARCHIVE_LIBS"
                    AC_MSG_CHECKING([whether for archive_entry_hardlink_is_set])
                    AC_LINK_IFELSE([AC_LANG_PROGRAM([[#include <archive.h>
                                 #include <archive_entry.h>]], [[archive_entry_hardlink_is_set(NULL);]])],[AC_DEFINE([HAVE_ARCHIVE_ENTRY_HARDLINK_IS_SET],
                                          [1], [Define if you have archive_entry_hardlink_is_set])
                                 AC_MSG_RESULT([yes])],[AC_MSG_RESULT([no])])
                    LIBS="$save_LIBS"
                  ],
                  [
                    AC_MSG_FAILURE([libarchive is required])
                  ])

PKG_CHECK_MODULES([LIBZ], [zlib], [
  AC_DEFINE([HAVE_LIBZ], [1], [Define if you have zlib])
  LIBZ="yes"
])

AS_IF([test "x${enable_qmanifest}" != "xno"], [
  AC_MSG_CHECKING([whether to enable qmanifest])
  AS_IF([test "x${LIBBL2}${LIBZ}${GPGME}" = "xyesyesyes"], [
    AC_MSG_RESULT([yes])
  ], [
    AC_MSG_RESULT([no: missing dependencies])
  ])
], [
  AC_MSG_CHECKING([whether to enable qmanifest])
  AC_MSG_RESULT([no: disabled by configure argument])
])

do_qmanifest=""
AM_CONDITIONAL([QMANIFEST_ENABLED], [test "x$enable_qmanifest" != xno])
if test "x$enable_qmanifest" != xno ; then
	AC_DEFINE([ENABLE_QMANIFEST], [1],
			  [Define if qmanifest should be compiled])
	do_qmanifest="yes"
fi

AS_IF([test "x${enable_gpkg}" != "xno"], [
  AC_MSG_CHECKING([whether to enable gpkg])
  AS_IF([test "x${LIBARCHIVE}" = "xyes"], [
    AS_IF([test "x${GPGME}" = "xyes"],
          [AC_MSG_RESULT([yes])],
          [AC_MSG_RESULT([yes, without OpenPGP signature verification (no gpgme)])])
  ], [
    AC_MSG_RESULT([no: missing dependencies])
    enable_gpkg=no
  ])
], [
  AC_MSG_CHECKING([whether to enable gpkg])
  AC_MSG_RESULT([no: disabled by configure argument])
])

do_gpkg=""
AM_CONDITIONAL([GPKG_ENABLED], [test "x$enable_gpkg" != xno])
if test "x$enable_gpkg" != xno ; then
	AC_DEFINE([ENABLE_GPKG], [1],
			  [Define if gpkg should be compiled])
	do_gpkg="yes"
fi

AS_IF([test "x${enable_gtree}" != "xno"], [
  AC_MSG_CHECKING([whether to enable gtree])
  AS_IF([test "x${GPGME}${LIBARCHIVE}" = "xyesyes"], [
    AC_MSG_RESULT([yes])
  ], [
    AC_MSG_RESULT([no: missing dependencies])
  ])
], [
  AC_MSG_CHECKING([whether to enable gtree])
  AC_MSG_RESULT([no: disabled by configure argument])
])

do_gtree=""
AM_CONDITIONAL([GTREE_ENABLED], [test "x$enable_gtree" != xno])
if test "x$enable_gtree" != xno ; then
	AC_DEFINE([ENABLE_GTREE], [1],
			  [Define if gtree should be compiled])
	do_gtree="yes"
fi
do_gpgme=""
if test "x$GPGME" = xyes ; then
	do_gpgme="yes"
fi
AC_SUBST([QMANIFEST_ENABLED], ["$do_qmanifest"])
AC_SUBST([GPKG_ENABLED], ["$do_gpkg"])
AC_SUBST([GTREE_ENABLED], ["$do_gtree"])
AC_SUBST([GPGME_ENABLED], ["$do_gpgme"])
AC_SUBST([CURL_ENABLED], ["$do_curl"])

AX_CFLAGS_WARN_ALL([CWFLAGS])
AC_DEFUN([PT_CHECK_CFLAG],[AX_CHECK_COMPILER_FLAGS([$1],[CFLAGS="$CFLAGS $1"])])
m4_foreach_w([flag], [
	-Wbad-function-cast
	-Wcast-align
	-Wchar-subscripts
	-Wcomment
	-Wdiscarded-qualifiers
	-Wextra
	-Wformat=2
	-Wimplicit
	-Winline
	-Wmissing-declarations
	-Wnested-externs
	-Wno-sign-compare
	-Wold-style-definition
	-Wsequence-point
	-Wshadow
	-Wunused
	-Wwrite-strings
], [
	AX_CHECK_COMPILE_FLAG(flag, AS_VAR_APPEND([CWFLAGS], " flag"))
])
dnl --enable-werror: treat warnings in our own code as errors (CI sanity
dnl gate).  CWFLAGS is applied only to portage-utils sources + libq, never
dnl to gnulib or the internal curl, so this does not fail on their warnings.
AC_ARG_ENABLE([werror],
  [AS_HELP_STRING([--enable-werror],
    [treat warnings in portage-utils own code as errors (does not affect gnulib or the internal curl)])])
dnl hash.c carries deliberate `#pragma omp` sections; with --disable-openmp
dnl (OPENMP_CFLAGS empty) -Wall flags them as unknown pragmas, which -Werror
dnl would then make fatal.  They are intentional no-ops without OpenMP, not a
dnl code-quality signal, so silence just that warning under the werror gate.
AS_IF([test "x${enable_werror}" = "xyes"],
  [AX_CHECK_COMPILE_FLAG([-Wno-unknown-pragmas],
    [AS_VAR_APPEND([CWFLAGS], " -Wno-unknown-pragmas")])
   AX_CHECK_COMPILE_FLAG([-Werror],
    [AS_VAR_APPEND([CWFLAGS], " -Werror")],
    [AC_MSG_WARN([-Werror not supported by this compiler; ignoring])])])
AC_SUBST([CWFLAGS], ["$CWFLAGS"])

AS_IF([test "x${enable_static}" = "xyes"],
      [AS_CASE([" $LIBARCHIVE_LIBS "],
        [*" -lxml2 "*],
        [PKG_CHECK_MODULES([STATICXML2], [libxml-2.0],
          [AS_VAR_APPEND([LIBARCHIVE_LIBS], [" $STATICXML2_LIBS -lstdc++"])],
          [AC_MSG_NOTICE([libxml-2.0.pc not found; static link may miss libarchive's transitive xml2/icu deps])])])
       AX_CHECK_LINK_FLAG([-static],
        [AS_VAR_APPEND([LDFLAGS], [" -static"])],
        [AC_MSG_ERROR([--enable-static requested but the toolchain cannot link "-static"; install a static libc])])
       pt_objdump=`command -v ${OBJDUMP:-${ac_tool_prefix}objdump} 2>/dev/null || command -v objdump 2>/dev/null || command -v llvm-objdump 2>/dev/null || echo :`
       pt_strings=`command -v ${STRINGS:-${ac_tool_prefix}strings} 2>/dev/null || command -v strings 2>/dev/null || command -v llvm-strings 2>/dev/null || echo :`
       pt_qfile=`command -v qfile 2>/dev/null || echo :`
       pt_static_libs="$LIBARCHIVE_LIBS $LIBZ_LIBS"
       pt_static_cflags="$LIBARCHIVE_CFLAGS $LIBZ_CFLAGS"
       pt_static_inc='#include <archive.h>
#include <zlib.h>'
       pt_static_body='struct archive *ar = archive_read_new(); archive_read_support_format_all(ar); archive_read_support_filter_all(ar); zlibVersion();'
       pt_static_hint=
       AS_IF([test "x${GPGME}" = "xyes"],
        [pt_static_libs="$pt_static_libs $GPGME_LIBS"
         pt_static_cflags="$pt_static_cflags $GPGME_CFLAGS"
         pt_static_inc="$pt_static_inc
#include <gpgme.h>"
         pt_static_body="$pt_static_body gpgme_ctx_t gctx; gpgme_check_version(NULL); gpgme_new(&gctx);"])
       AS_IF([test "x${LIBBL2}" = "xyes"],
        [pt_static_libs="$pt_static_libs $LIBBL2_LIBS"
         pt_static_cflags="$pt_static_cflags $LIBBL2_CFLAGS"
         pt_static_inc="$pt_static_inc
#include <blake2.h>"
         pt_static_body="$pt_static_body blake2b_state bs; blake2b_init(&bs, 64);"])
       AS_IF([test "x${do_curl}" = "xyes" && test "x${pt_internal_curl}" != "xyes"],
        [pt_static_libs="$pt_static_libs $LIBCURL_LIBS"
         pt_static_cflags="$pt_static_cflags $LIBCURL_CFLAGS"
         pt_static_inc="$pt_static_inc
#include <curl/curl.h>"
         pt_static_body="$pt_static_body CURL *cu = curl_easy_init(); curl_version(); curl_easy_cleanup(cu);"
         pt_static_hint='
  or use --enable-internal-libs with a curl source tree in src/curl'])

       pt_cc_name=`set dummy $CC; echo "$2"`
       pt_cc_major=`$CC -dumpversion 2>/dev/null | sed 's/\..*//'`
       pt_static_seen=
       pt_static_missing=
       pt_static_stale=
       AC_MSG_CHECKING([for the static archives of the dependency closure])
       for pt_l in $pt_static_libs; do
         AS_CASE([$pt_l], [-l*],
          [pt_n=`echo "$pt_l" | sed 's/^-l//'`
           AS_CASE([" $pt_static_seen "], [*" $pt_n "*], [continue])
           pt_static_seen="$pt_static_seen $pt_n"
           pt_p=`$CC $LDFLAGS -print-file-name=lib$pt_n.a 2>/dev/null`
           AS_CASE([$pt_p], [/*],
            [AS_IF([$pt_objdump -h "$pt_p" 2>/dev/null | grep '\.gnu\.lto_' >/dev/null 2>&1],
              [pt_v=`$pt_strings "$pt_p" 2>/dev/null | sed -n 's/^GCC: (.*) \(@<:@0-9@:>@*\)\..*/\1/p' | sort -u | grep -v "^$pt_cc_major\$" | head -n 1`
               AS_IF([test -n "$pt_v"],
                [pt_o=`$pt_qfile -q "$pt_p" 2>/dev/null | head -n 1`
                 pt_static_stale="$pt_static_stale
    lib$pt_n.a (gcc $pt_v${pt_o:+, $pt_o})"])])],
            [pt_static_missing="$pt_static_missing lib$pt_n.a"])])
       done
       AS_IF([test -n "$pt_static_missing"],
        [AC_MSG_RESULT([no])
         AC_MSG_ERROR([--enable-static: no static archive for:$pt_static_missing
  build them with USE=static-libs$pt_static_hint])])
       AC_MSG_RESULT([yes])

       AC_MSG_CHECKING([whether the static dependency closure links])
       pt_save_CFLAGS=$CFLAGS
       pt_save_LIBS=$LIBS
       CFLAGS="$CFLAGS $pt_static_cflags"
       LIBS="$pt_static_libs $LIBS"
       AC_LANG_CONFTEST([AC_LANG_PROGRAM([[$pt_static_inc]], [[$pt_static_body]])])
       AS_IF([(eval "$ac_link") 2>conftest.lto && test -x conftest$ac_exeext],
        [AC_MSG_RESULT([yes])
         AS_IF([test -n "$pt_static_stale"],
          [AC_MSG_WARN([static archives hold LTO bytecode of another compiler than $pt_cc_name $pt_cc_major, the link of q may fail on them:$pt_static_stale])])],
        [AC_MSG_RESULT([no])
         cat conftest.lto >&AS_MESSAGE_LOG_FD
         pt_lto=`sed -n "s/.*bytecode stream in file \(.*\) generated with LTO version \(.*\) instead of the expected \(.*\)\$/    \1 holds LTO \2, $pt_cc_name reads LTO \3/p" conftest.lto | sort -u`
         pt_err=`grep -E 'undefined reference|cannot find|error' conftest.lto | head -n 5`
         rm -f conftest.lto conftest.$ac_ext conftest$ac_exeext conftest.$ac_objext
         AS_IF([test -n "$pt_lto"],
          [pt_static_stale="
$pt_lto$pt_static_stale"])
         AS_IF([test -n "$pt_static_stale"],
          [AC_MSG_ERROR([--enable-static: the dependency closure cannot be linked statically, static archives hold LTO bytecode of another compiler than $pt_cc_name $pt_cc_major:$pt_static_stale
  rebuild them with the compiler in use; a gcc major bump breaks every archive built with -flto, fat ones too])],
          [AC_MSG_ERROR([--enable-static: the dependency closure cannot be linked statically (see config.log):
$pt_err$pt_static_hint])])])
       rm -f conftest.lto conftest.$ac_ext conftest$ac_exeext conftest.$ac_objext
       CFLAGS=$pt_save_CFLAGS
       LIBS=$pt_save_LIBS])

AC_CONFIG_FILES([
	Makefile
	libq/Makefile
	autotools/gnulib/Makefile
	tests/init.sh
	tests/Makefile
	tests/atom_compare/Makefile
	tests/atom_explode/Makefile
	tests/copy_file/Makefile
	tests/fuzz/Makefile
	tests/install/Makefile
	tests/mkdir/Makefile
	tests/profile/Makefile
	tests/qatom/Makefile
	tests/qcheck/Makefile
	tests/qdepends/Makefile
	tests/qetc-update/Makefile
	tests/qetuto/Makefile
	tests/qfile/Makefile
	tests/qgrep/Makefile
	tests/qkeyword/Makefile
	tests/qlist/Makefile
	tests/qlop/Makefile
	tests/qmaint/Makefile
	tests/qmanifest/Makefile
	tests/qmerge/Makefile
	tests/qnews/Makefile
	tests/qsearch/Makefile
	tests/qsize/Makefile
	tests/qtbz2/Makefile
	tests/qtegrity/Makefile
	tests/quse/Makefile
	tests/qwhich/Makefile
	tests/qxpak/Makefile
	tests/rmspace/Makefile
	tests/source/Makefile
	tests/usedep/Makefile
	tests/preserved/Makefile
])
AC_OUTPUT

# vim: set ts=2 sw=2 softtabstop=2 expandtab:
