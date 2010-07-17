dnl config.m4 for extension msgpack

dnl Comments in this file start with the string 'dnl'.
dnl Remove where necessary. This file will not work
dnl without editing.

dnl Check PHP version:

AC_MSG_CHECKING(PHP version)
AC_TRY_COMPILE([#include "php/main/php_version.h"], [
#if PHP_MAJOR_VERSION < 5 || (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION < 2)
#error  this extension requires at least PHP version 5.2.0
#endif
],
[AC_MSG_RESULT(ok)],
[AC_MSG_ERROR([need at least PHP 5.2.0])])

dnl If your extension references something external, use with:

PHP_ARG_WITH(msgpack, for msgpack support,
Make sure that the comment is aligned:
[  --with-msgpack             Include msgpack support])

dnl PHP_ARG_ENABLE(msgpack, whether to enable msgpack support,
dnl Make sure that the comment is aligned:
dnl [  --enable-msgpack           Enable msgpack support])

if test "$PHP_MSGPACK" != "no"; then
  dnl Write more examples of tests here...

  dnl --with-msgpack -> check with-path
  SEARCH_PATH="/usr/local /usr"     # you might want to change this
  SEARCH_FOR="/include/msgpack.h"  # you most likely want to change this
  if test -r $PHP_MSGPACK/$SEARCH_FOR; then # path given as parameter
    MSGPACK_DIR=$PHP_MSGPACK
  else # search default path list
    AC_MSG_CHECKING([for msgpack files in default path])
    for i in $SEARCH_PATH ; do
      if test -r $i/$SEARCH_FOR; then
        MSGPACK_DIR=$i
        AC_MSG_RESULT(found in $i)
      fi
    done
  fi

  if test -z "$MSGPACK_DIR"; then
    AC_MSG_RESULT([not found])
    AC_MSG_ERROR([Please reinstall the msgpack distribution])
  fi

  dnl --with-msgpack -> add include path
  PHP_ADD_INCLUDE($MSGPACK_DIR/include)

  dnl --with-msgpack -> check for lib and symbol presence
  LIBNAME=msgpack # you may want to change this
  LIBSYMBOL=msgpack_pack_object # you most likely want to change this 

  PHP_CHECK_LIBRARY($LIBNAME,$LIBSYMBOL,
  [
    PHP_ADD_LIBRARY_WITH_PATH($LIBNAME, $MSGPACK_DIR/lib, MSGPACK_SHARED_LIBADD)
    AC_DEFINE(HAVE_MSGPACKLIB,1,[ ])
  ],[
    AC_MSG_ERROR([wrong msgpack lib version or lib not found])
  ],[
    -L$MSGPACK_DIR/lib -lm
  ])

  PHP_SUBST(MSGPACK_SHARED_LIBADD)

  PHP_NEW_EXTENSION(msgpack, msgpack.c msgpack_pack.c msgpack_unpack.c msgpack_class.c, $ext_shared)

  PHP_INSTALL_HEADERS([ext/msgpack], [php_msgpack.h])
fi
