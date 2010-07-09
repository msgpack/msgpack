
AM_CPPFLAGS   = -I../src
AM_C_CPPFLAGS = -I../src
AM_LDFLAGS = ../src/libmsgpack.la -lgtest_main

check_PROGRAMS = \
		zone \
		pack_unpack \
		pack_unpack_c \
		streaming \
		streaming_c \
		object \
		convert \
		buffer \
		cases \
		version \
		msgpackc_test \
		msgpack_test

TESTS = $(check_PROGRAMS)

zone_SOURCES = zone.cc

pack_unpack_SOURCES = pack_unpack.cc

pack_unpack_c_SOURCES = pack_unpack_c.cc

streaming_SOURCES = streaming.cc

streaming_c_SOURCES = streaming_c.cc

object_SOURCES = object.cc

convert_SOURCES = convert.cc

buffer_SOURCES = buffer.cc
buffer_LDADD = -lz

cases_SOURCES = cases.cc

version_SOURCES = version.cc

msgpackc_test_SOURCES = msgpackc_test.cpp

msgpack_test_SOURCES = msgpack_test.cpp

EXTRA_DIST = cases.mpac cases_compact.mpac

