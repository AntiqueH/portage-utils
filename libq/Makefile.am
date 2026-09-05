
QFILES = \
	array.c array.h \
	atom.c atom.h \
	basename.c basename.h \
	binpath.c binpath.h \
	binrepos.c binrepos.h \
	busybox.h \
	colors.c colors.h \
	contents.c contents.h \
	copy_file.c copy_file.h \
	dep.c dep.h \
	eat_file.c eat_file.h \
	elfneeded.c elfneeded.h \
	envd.c envd.h \
	file_magic.c file_magic.h \
	gpgsign.c gpgsign.h \
	gpkg.c gpkg.h \
	hash.c hash.h \
	human_readable.c human_readable.h \
	mfline.c mfline.h \
	move_file.c move_file.h \
	moves.c moves.h \
	prelink.c prelink.h \
	profile.c profile.h \
	rmspace.c rmspace.h \
	safe_io.c safe_io.h \
	scandirat.c scandirat.h \
	set.c set.h \
	tree.c tree.h \
	usedep.c usedep.h \
	preserved.c preserved.h \
	linkage.c linkage.h \
	useflags.c useflags.h \
	xasprintf.h \
	xchdir.c xchdir.h \
	xmkdir.c xmkdir.h \
	xpak.c xpak.h \
	xregex.c xregex.h \
	xsystem.c xsystem.h \
	$(NULL)

noinst_LIBRARIES = libq.a
libq_a_SOURCES = $(QFILES)
libq_a_CPPFLAGS = \
	$(OPENMP_CFLAGS) \
	-I$(top_builddir)/autotools/gnulib \
	-I$(top_srcdir)/autotools/gnulib \
	-I$(top_srcdir) \
	$(CWFLAGS)
