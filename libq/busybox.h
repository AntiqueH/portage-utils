/* some hax defines to help import busybox */
#ifndef BUSYBOX_H
#define BUSYBOX_H

#define CONFIG_MD5SUM
#define CONFIG_SHA1SUM

#define HASH_SHA1	1
#define HASH_MD5	2

#define bb_full_read(fd, buf, count) read(fd, buf, count)

#endif /* BUSYBOX_H */
