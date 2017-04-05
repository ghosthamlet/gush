AC_INIT([gush], [0.1.0], [cwebber@dustycloud.org])

AM_INIT_AUTOMAKE([-Wall -Werror foreign])

m4_ifdef([GUILE_PROGS],
         [],
         [AC_ERROR(could not locate guile aclocal macros)])

GUILE_PKG([2.2 2.0])
GUILE_PROGS

AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([pre-inst-env], [chmod +x pre-inst-env])
AC_OUTPUT
