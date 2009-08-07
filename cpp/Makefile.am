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
		msgpack/type/array.hpp \
		msgpack/type/boolean.hpp \
		msgpack/type/float.hpp \
		msgpack/type/integer.hpp \
		msgpack/type/map.hpp \
		msgpack/type/nil.hpp \
		msgpack/type/raw.hpp \
		msgpack/type/tuple.hpp \
		msgpack/type/define.hpp

# FIXME
object.lo: msgpack/type/tuple.hpp msgpack/zone.hpp

msgpack/type/tuple.hpp: msgpack/type/tuple.hpp.erb
	$(ERB) $< > $@.tmp
	mv $@.tmp $@

msgpack/type/define.hpp: msgpack/type/define.hpp.erb
	$(ERB) $< > $@.tmp
	mv $@.tmp $@

msgpack/zone.hpp: msgpack/zone.hpp.erb
	$(ERB) $< > $@.tmp
	mv $@.tmp $@

MOSTLYCLEANFILES = \
		msgpack/type/tuple.hpp \
		msgpack/type/define.hpp \
		msgpack/zone.hpp

EXTRA_DIST = \
		msgpack/type/tuple.hpp.erb \
		msgpack/type/define.hpp.erb \
		msgpack/zone.hpp.erb

libmsgpack_la_LIBADD = -L../c -lmsgpackc

# -version-info CURRENT:REVISION:AGE
libmsgpack_la_LDFLAGS = -version-info 1:0:0

