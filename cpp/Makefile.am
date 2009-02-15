lib_LTLIBRARIES = libmsgpack.la

libmsgpack_la_SOURCES = \
		object.cpp \
		unpack.cpp \
		zone.cpp

nobase_include_HEADERS = \
		msgpack.hpp \
		msgpack/pack.hpp \
		msgpack/unpack.hpp \
		msgpack/object.hpp \
		msgpack/zone.hpp

noinst_HEADERS = \
		msgpack/zone.hpp.erb

# FIXME
object.lo: msgpack/zone.hpp
unpack.lo: msgpack/zone.hpp
zone.lo: msgpack/zone.hpp

msgpack/zone.hpp: msgpack/zone.hpp.erb
	erb $< > $@

MOSTLYCLEANFILES = zone.hpp

libmsgpack_la_LDFLAGS = -version-info 0:0:0

