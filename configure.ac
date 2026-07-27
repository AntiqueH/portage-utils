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

dnl the codebase must stay buildable as ISO C99 so it remains widely
dnl adoptable (older GCC, and non-GNU compilers alike): force -std=c99
dnl so any C11+ construct or GNU language extension is rejected at
dnl compile time.  POSIX/GNU *APIs* stay available through
dnl AC_USE_SYSTEM_EXTENSIONS (_GNU_SOURCE et al override strict-ANSI
dnl header gating).  This must sit directly after AC_PROG_CC so all
dnl subsequent feature tests (gnulib in particular) probe the compiler
dnl at the same language level.  A -std= supplied in CFLAGS wins.
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
AC_USE_SYSTEM_EXTENSIONS
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

dnl libcurl: default to the bundled copy in src/curl, but let distributions
dnl link the system libcurl instead with --with-system-libcurl
AC_ARG_WITH([system-libcurl],
  [AS_HELP_STRING([--with-system-libcurl],
    [link against the system libcurl instead of the bundled copy in src/curl])],
  [with_system_libcurl=$withval], [with_system_libcurl=no])

AS_IF([test "x${with_system_libcurl}" = "xyes"],
  [
    PKG_CHECK_MODULES([LIBCURL], [libcurl],
                      [AC_MSG_NOTICE([using system libcurl])],
                      [AC_MSG_FAILURE([--with-system-libcurl given but libcurl.pc could not be found])])
  ],
  [
    dnl dependencies of the vendored libcurl in src/curl (HTTP(S)-only)
    PKG_CHECK_MODULES([VCURL_DEPS], [openssl zlib],
                      [],
                      [AC_MSG_FAILURE([openssl and zlib are required (vendored libcurl)])])
  ])

AM_CONDITIONAL([SYSTEM_LIBCURL], [test "x${with_system_libcurl}" = "xyes"])

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
                    AS_IF([test "x${enable_gpkg}" = "xyes"],
                          [
                            AC_MSG_FAILURE([--enable-gpkg was given, but libarchive.pc could not be found])
                          ])
                    AS_IF([test "x${enable_gtree}" = "xyes"],
                          [
                            AC_MSG_FAILURE([--enable-gtree was given, but libarchive.pc could not be found])
                          ])
                    LIBARCHIVE="no: missing dependencies"
                    enable_gpkg=no
                    enable_gtree=no
                  ])

AS_IF([test "x${enable_qmanifest}" != "xno"], [
  PKG_CHECK_MODULES([LIBZ], [zlib], [
    AC_DEFINE([HAVE_LIBZ], [1], [Define if you have zlib])
    LIBZ="yes"
  ], [
    AS_IF([test "x${enable_qmanifest}" = "xyes"], [
      AC_MSG_FAILURE([--enable-qmanifest was given, but zlib.pc could not be found])
    ])
    LIBZ="no: missing dependencies"
    enable_qmanifest=no
  ])

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
AC_SUBST([QMANIFEST_ENABLED], ["$do_qmanifest"])
AC_SUBST([GPKG_ENABLED], ["$do_gpkg"])
AC_SUBST([GTREE_ENABLED], ["$do_gtree"])

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
dnl to the vendored gnulib/curl, so this does not fail on their warnings.
AC_ARG_ENABLE([werror],
  [AS_HELP_STRING([--enable-werror],
    [treat warnings in portage-utils own code as errors (does not affect vendored gnulib/curl)])])
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

AC_CONFIG_FILES([
	src/curl/Makefile
	Makefile
	libq/Makefile
	autotools/gnulib/Makefile
	tests/init.sh
	tests/Makefile
	tests/atom_compare/Makefile
	tests/atom_explode/Makefile
	tests/copy_file/Makefile
	tests/install/Makefile
	tests/mkdir/Makefile
	tests/profile/Makefile
	tests/qatom/Makefile
	tests/qcheck/Makefile
	tests/qdepends/Makefile
	tests/qfile/Makefile
	tests/qlist/Makefile
	tests/qlop/Makefile
	tests/qmanifest/Makefile
	tests/qmerge/Makefile
	tests/qtbz2/Makefile
	tests/quse/Makefile
	tests/qxpak/Makefile
	tests/rmspace/Makefile
	tests/source/Makefile
])
AC_OUTPUT

# vim: set ts=2 sw=2 softtabstop=2 expandtab:
