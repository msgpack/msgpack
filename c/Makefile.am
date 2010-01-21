lib_LTLIBRARIES = libmsgpackc.la

libmsgpackc_la_SOURCES = \
		unpack.c \
		object.c \
		vrefbuffer.c \
		zone.c

nobase_include_HEADERS = \
		msgpack.h \
		msgpack/sbuffer.h \
		msgpack/vrefbuffer.h \
		msgpack/pack.h \
		msgpack/unpack.h \
		msgpack/object.h \
		msgpack/zone.h

# -version-info CURRENT:REVISION:AGE
libmsgpackc_la_LDFLAGS = -version-info 2:0:0

check_PROGRAMS = \
  msgpackc_test

msgpackc_test_SOURCES = test.cpp
msgpackc_test_CXXFLAGS = -I$(top_srcdir) -I$(top_srcdir)/c
msgpackc_test_LDADD = libmsgpackc.la -lgtest_main

TESTS = $(check_PROGRAMS)
