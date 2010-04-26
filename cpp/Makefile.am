
lib_LTLIBRARIES = libmsgpack.la

libmsgpack_la_SOURCES = \
		unpack.c \
		objectc.c \
		vrefbuffer.c \
		zone.c \
		object.cpp

# -version-info CURRENT:REVISION:AGE
libmsgpack_la_LDFLAGS = -version-info 3:0:0


# backward compatibility
lib_LTLIBRARIES += libmsgpackc.la

libmsgpackc_la_SOURCES = \
		unpack.c \
		objectc.c \
		vrefbuffer.c \
		zone.c

libmsgpackc_la_LDFLAGS = -version-info 2:0:0

# work around for duplicated file name
kumo_manager_CFLAGS = $(AM_CFLAGS)
kumo_manager_CXXFLAGS = $(AM_CXXFLAGS)


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


EXTRA_DIST = \
		README.md \
		LICENSE \
		NOTICE \
		msgpack_vc8.vcproj \
		msgpack_vc8.sln \
		msgpack_vc8.postbuild.bat

SUBDIRS = test

check_PROGRAMS = \
		msgpackc_test \
		msgpack_test

msgpackc_test_SOURCES = msgpackc_test.cpp
msgpackc_test_LDADD = libmsgpack.la -lgtest_main

msgpack_test_SOURCES = msgpack_test.cpp
msgpack_test_LDADD = libmsgpack.la -lgtest_main

TESTS = $(check_PROGRAMS)

