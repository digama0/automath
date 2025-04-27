/* stupid flex */

#include <stdlib.h>
#include <unistd.h>

#define YY_NO_UNISTD_H
#define exit(status) (status, flexexit())
#define isatty(fd) (fd, flexisatty())

void flexexit() { exit(2); }

int flexisatty() { return 0; }
