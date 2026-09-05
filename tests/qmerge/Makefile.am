this_subdir = tests/qmerge
s = $(abs_top_srcdir)/$(this_subdir)

check_PROGRAMS = qmerge-httpd
qmerge_httpd_SOURCES = httpd.c

check-local: qmerge-httpd
	$(Q)$(s)/dotest