this_subdir = tests/fuzz
s = $(abs_top_srcdir)/$(this_subdir)

AM_DEFAULT_SOURCE_EXT = .c

AM_CPPFLAGS = \
	-I$(top_srcdir) \
	-I$(top_srcdir)/libq \
	-I$(top_builddir)/autotools/gnulib \
	-I$(top_srcdir)/autotools/gnulib \
	$(OPENMP_CFLAGS) \
	$(LIBBL2_CFLAGS) \
	$(LIBZ_CFLAGS) \
	$(LIBARCHIVE_CFLAGS) \
	-DFUZZ_SRCDIR=\"$(s)\" \
	$(NULL)

if QMANIFEST_ENABLED
AM_CPPFLAGS += $(GPGME_CFLAGS)
endif

noinst_LIBRARIES = libfuzzdrv.a
libfuzzdrv_a_SOURCES = main.c

LDADD = \
	libfuzzdrv.a \
	$(top_builddir)/libq/libq.a \
	$(top_builddir)/autotools/gnulib/libgnu.a \
	$(OPENMP_CFLAGS) \
	$(LIBBL2_LIBS) \
	$(LIBZ_LIBS) \
	$(GPGME_LIBS) \
	$(LIBARCHIVE_LIBS) \
	$(LIB_CRYPTO) \
	$(LIB_CLOCK_GETTIME) \
	$(LIB_EACCESS) \
	$(SENDFILE_LIBS) \
	$(NULL)

check_PROGRAMS = \
	fuzz_atom \
	fuzz_binpath \
	fuzz_binrepos \
	fuzz_contents \
	fuzz_dep \
	fuzz_elfneeded \
	fuzz_envd \
	fuzz_hash \
	fuzz_mfline \
	fuzz_moves \
	fuzz_needed \
	fuzz_packages \
	fuzz_preserved \
	fuzz_usedep \
	fuzz_useflags \
	fuzz_xpak \
	$(NULL)

if GPKG_ENABLED
check_PROGRAMS += \
	fuzz_gpkg_manifest \
	fuzz_gpkg_structure
endif

TESTS = $(check_PROGRAMS)
