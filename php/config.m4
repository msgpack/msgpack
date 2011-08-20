dnl config.m4 for extension msgpack

dnl Comments in this file start with the string 'dnl'.
dnl Remove where necessary. This file will not work
dnl without editing.

dnl Check PHP version:

AC_MSG_CHECKING(PHP version)
AC_TRY_COMPILE([#include "$phpincludedir/main/php_version.h"], [
#if PHP_MAJOR_VERSION < 5
#error  this extension requires at least PHP version 5 or newer
#endif
],
[AC_MSG_RESULT(ok)],
[AC_MSG_ERROR([need at least PHP 5 or newer])])

dnl If your extension references something external, use with:

PHP_ARG_WITH(msgpack, for msgpack support,
Make sure that the comment is aligned:
[  --with-msgpack             Include msgpack support])

if test "$PHP_MSGPACK" != "no"; then
  PHP_NEW_EXTENSION(msgpack, msgpack.c msgpack_pack.c msgpack_unpack.c msgpack_class.c msgpack_convert.c, $ext_shared)

  ifdef([PHP_INSTALL_HEADERS],
  [
    PHP_INSTALL_HEADERS([ext/msgpack], [php_msgpack.h])
  ], [
    PHP_ADD_MAKEFILE_FRAGMENT
  ])
fi
