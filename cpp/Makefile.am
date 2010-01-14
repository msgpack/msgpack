lib_LTLIBRARIES = libmsgpack.la

libmsgpack_la_SOURCES = \
		object.cpp

nobase_include_HEADERS = \
		msgpack.hpp \
		msgpack/sbuffer.hpp \
		msgpack/vrefbuffer.hpp \
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

libmsgpack_la_LIBADD = -L../c -lmsgpackc

# -version-info CURRENT:REVISION:AGE
libmsgpack_la_LDFLAGS = -version-info 1:0:0

check_PROGRAMS = \
  msgpack_test

msgpack_test_SOURCES = test.cpp
msgpack_test_CXXFLAGS = -I$(top_srcdir) -I$(top_srcdir)/c -I$(top_srcdir)/cpp
msgpack_test_LDFLAGS = libmsgpack.la -lgtest_main

TESTS = $(check_PROGRAMS)
