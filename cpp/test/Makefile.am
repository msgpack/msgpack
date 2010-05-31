
AM_CPPFLAGS   = -I../src
AM_C_CPPFLAGS = -I../src
AM_LDFLAGS = ../src/libmsgpack.la -lgtest_main

check_PROGRAMS = \
		zone \
		pack_unpack \
		streaming \
		object \
		convert \
		buffer \
		cases \
		msgpackc_test \
		msgpack_test

TESTS = $(check_PROGRAMS)

zone_SOURCES = zone.cc

pack_unpack_SOURCES = pack_unpack.cc

streaming_SOURCES = streaming.cc

object_SOURCES = object.cc

convert_SOURCES = convert.cc

buffer_SOURCES = buffer.cc
buffer_LDADD = -lz

cases_SOURCES = cases.cc

msgpackc_test_SOURCES = msgpackc_test.cpp

msgpack_test_SOURCES = msgpack_test.cpp

EXTRA_DIST = cases.mpac cases_compact.mpac

