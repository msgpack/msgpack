dnl $Id$
dnl config.m4 for extension msgpack

PHP_ARG_ENABLE(msgpack, whether to enable MessagePack support,
Make sure that the comment is aligned:
[  --enable-msgpack           Enable MessagePack support])

if test "$PHP_MSGPACK" != "no"; then
  dnl AC_DEFINE([HAVE_MSGPACK],1 ,[whether to enable MessagePack support])
  dnl AC_HEADER_STDC

  PHP_NEW_EXTENSION(msgpack, msgpack.c, $ext_shared)
  dnl PHP_SUBST(MSGPACK_SHARED_LIBADD)
fi
