lib_LTLIBRARIES = libmsgpack.la

libmsgpack_la_SOURCES = \
		object.cpp \
		unpack.cpp \
		unpack_inline.cpp \
		zone.cpp

nobase_include_HEADERS = \
		msgpack/pack.hpp \
		msgpack/unpack.hpp \
		msgpack/object.hpp \
		msgpack/zone.hpp

noinst_HEADERS = \
		unpack_context.hpp

zone.hpp: zone.hpp.erb
	erb $< > $@

