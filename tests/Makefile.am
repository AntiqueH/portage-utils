SUBDIRS = \
	atom_compare atom_explode copy_file fuzz mkdir rmspace usedep preserved \
	qatom qcheck qdepends qetc-update qetuto qfile qgrep qkeyword qlist qlop qmerge \
	qnews qsearch qsize qtbz2 qtegrity quse qwhich qxpak \
	install profile

if QMANIFEST_ENABLED
SUBDIRS += qmanifest
endif

SUBDIRS += source

%_subdir:
	$(Q)cd $(@:_subdir=) || exit 1; \
	out=`$(MAKE) check 2>&1`; \
	ret=$$?; \
	echo "$$out"; \
	exit $$ret
