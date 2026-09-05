ACLOCAL_AMFLAGS = -I autotools/m4

if INTERNAL_CURL
CURL_CPPFLAGS = -I$(top_srcdir)/src/curl/include -DCURL_STATICLIB
INTERNAL_CURL_BUILD = $(top_builddir)/internal-libs/curl
INTERNAL_CURL_LIB = $(INTERNAL_CURL_BUILD)/lib/.libs/libcurl.a
CURL_LIBS = $(INTERNAL_CURL_LIB) $(INTERNAL_CURL_LIBS)
BUILT_SOURCES = internal-curl
INTERNAL_CURL_CLEAN = $(MAKE) $(AM_MAKEFLAGS) -C $(INTERNAL_CURL_BUILD)/lib clean
INTERNAL_CURL_DISTCLEAN = rm -rf $(top_builddir)/internal-libs
internal-curl:
	$(MAKE) $(AM_MAKEFLAGS) -C $(INTERNAL_CURL_BUILD)/lib
.PHONY: internal-curl
else
CURL_CPPFLAGS = $(LIBCURL_CFLAGS)
CURL_LIBS = $(LIBCURL_LIBS)
INTERNAL_CURL_CLEAN = :
INTERNAL_CURL_DISTCLEAN = :
endif

SUBDIRS = \
	autotools/gnulib \
	libq \
	. \
	tests \
	$(NULL)

APPLETS = \
	q \
	qatom \
	qcheck \
	qdepends \
	qfile \
	qgpkg-sign \
	qgrep \
	qkeyword \
	qlist \
	qlop \
	qmaint \
	qnews \
	qetuto \
	qmerge \
	qpkg \
	qsearch \
	qsize \
	qtbz2 \
	qtegrity \
	quse \
	qwhich \
	qxpak \
	$(NULL)

# man/*.1 are generated out-of-band by man/mkman.py and installed per applet
dist_man1_MANS = $(APPLETS:%=man/%.1) man/qetc-update.1

bin_PROGRAMS = q

dist_sbin_SCRIPTS = qetc-update

q_SOURCES = \
	main.c \
	q.c \
	qatom.c \
	qcheck.c \
	qdepends.c \
	qfile.c \
	qgpkg-sign.c \
	qgrep.c \
	qkeyword.c \
	qlist.c \
	qlop.c \
	qmaint.c \
	qnews.c \
	qetuto.c \
	qmerge.c \
	qpkg.c \
	qsearch.c \
	qsize.c \
	qtbz2.c \
	qtegrity.c \
	quse.c \
	qwhich.c \
	qxpak.c \
	$(NULL)
q_CPPFLAGS = \
	-I$(top_srcdir)/libq \
	-I$(top_builddir)/autotools/gnulib \
	-I$(top_srcdir)/autotools/gnulib \
	$(OPENMP_CFLAGS) \
	$(LIBBL2_CFLAGS) \
	$(LIBZ_CFLAGS) \
	$(LIBARCHIVE_CFLAGS) \
	$(CURL_CPPFLAGS) \
	$(CWFLAGS) \
	$(NULL)
q_LDADD = \
	$(top_builddir)/libq/libq.a \
	$(top_builddir)/autotools/gnulib/libgnu.a \
	$(OPENMP_CFLAGS) \
	$(LIBBL2_LIBS) \
	$(LIBZ_LIBS) \
	$(GPGME_LIBS) \
	$(LIBARCHIVE_LIBS) \
	$(CURL_LIBS) \
	$(LIB_CRYPTO) \
	$(LIB_CLOCK_GETTIME) \
	$(LIB_EACCESS) \
	$(SENDFILE_LIBS) \
	$(NULL)

if QMANIFEST_ENABLED
q_SOURCES += qmanifest.c
q_CPPFLAGS += \
	$(GPGME_CFLAGS)
APPLETS += qmanifest
endif

install-exec-hook:
	cd $(DESTDIR)$(bindir); \
	for applet in $(APPLETS) ; do \
		[ ! -e "$${applet}" ] && $(LN_S) q $${applet} ; \
	done

clean-local:
	rm -f $(APPLETS)
	-$(INTERNAL_CURL_CLEAN)

distclean-local:
	-$(INTERNAL_CURL_DISTCLEAN)

EXTRA_DIST = \
	autotools/m4/gnulib-cache.m4 \
	applets.h \
	tests \
	$(NULL)
