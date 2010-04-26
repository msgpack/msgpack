
AM_CPPFLAGS   = -I..
AM_C_CPPFLAGS = -I..
AM_LDFLAGS = ../libmsgpack.la -lgtest_main

check_PROGRAMS = \
		zone \
		pack_unpack \
		streaming \
		object \
		convert \
		buffer

TESTS = $(check_PROGRAMS)

zone_SOURCES = zone.cc

pack_unpack_SOURCES = pack_unpack.cc

streaming_SOURCES = streaming.cc

object_SOURCES = object.cc

convert_SOURCES = convert.cc

buffer_SOURCES = buffer.cc
buffer_LDADD = -lz

