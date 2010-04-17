lib_LTLIBRARIES = libmsgpackc.la libmsgpack.la

libmsgpackc_la_SOURCES = \
		unpack.c \
		object.c \
		vrefbuffer.c \
		zone.c

# -version-info CURRENT:REVISION:AGE
libmsgpackc_la_LDFLAGS = -version-info 2:0:0


libmsgpack_la_SOURCES = \
		object.cpp

libmsgpack_la_LIBADD = -lmsgpackc

# -version-info CURRENT:REVISION:AGE
libmsgpack_la_LDFLAGS = -version-info 2:0:0


nobase_include_HEADERS = \
		msgpack/pack_define.h \
		msgpack/pack_template.h \
		msgpack/unpack_define.h \
		msgpack/unpack_template.h \
		msgpack/sysdep.h \
		msgpack.h \
		msgpack/sbuffer.h \
		msgpack/vrefbuffer.h \
		msgpack/zbuffer.h \
		msgpack/pack.h \
		msgpack/unpack.h \
		msgpack/object.h \
		msgpack/zone.h \
		msgpack.hpp \
		msgpack/sbuffer.hpp \
		msgpack/vrefbuffer.hpp \
		msgpack/zbuffer.hpp \
		msgpack/pack.hpp \
		msgpack/unpack.hpp \
		msgpack/object.hpp \
		msgpack/zone.hpp \
		msgpack/type.hpp \
		msgpack/type/bool.hpp \
		msgpack/type/float.hpp \
		msgpack/type/int.hpp \
		msgpack/type/list.hpp \
		msgpack/type/deque.hpp \
		msgpack/type/map.hpp \
		msgpack/type/nil.hpp \
		msgpack/type/pair.hpp \
		msgpack/type/raw.hpp \
		msgpack/type/set.hpp \
		msgpack/type/string.hpp \
		msgpack/type/vector.hpp \
		msgpack/type/tuple.hpp \
		msgpack/type/define.hpp \
		msgpack/type/tr1/unordered_map.hpp \
		msgpack/type/tr1/unordered_set.hpp


# work around for duplicated object file name
libmsgpackc_la_CFLAGS = $(AM_CFLAGS)
libmsgpackc_la_CXXFLAGS = $(AM_CXXFLAGS)
libmsgpack_la_CFLAGS = $(AM_CFLAGS)
libmsgpack_la_CXXFLAGS = $(AM_CXXFLAGS)


EXTRA_DIST = \
		msgpack_vc8.vcproj \
		msgpack_vc8.sln \
		msgpack_vc8.postbuild.bat


check_PROGRAMS = \
		msgpackc_test \
		msgpack_test

msgpackc_test_SOURCES = msgpackc_test.cpp
msgpackc_test_CXXFLAGS = -I$(top_srcdir) -I$(top_srcdir)/c
msgpackc_test_LDADD = libmsgpackc.la -lgtest_main

msgpack_test_SOURCES = msgpack_test.cpp
msgpack_test_CXXFLAGS = -I$(top_srcdir) -I$(top_srcdir)/c -I$(top_srcdir)/cpp
msgpack_test_LDADD = libmsgpack.la -lgtest_main

TESTS = $(check_PROGRAMS)

