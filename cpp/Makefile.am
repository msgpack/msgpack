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
		msgpack/zone.hpp \
		msgpack/type.hpp \
		msgpack/type/array.hpp \
		msgpack/type/boolean.hpp \
		msgpack/type/float.hpp \
		msgpack/type/integer.hpp \
		msgpack/type/map.hpp \
		msgpack/type/nil.hpp \
		msgpack/type/raw.hpp \
		msgpack/type/tuple.hpp

noinst_HEADERS = \
		msgpack/type/tuple.hpp.erb

# FIXME
object.lo: msgpack/type/tuple.hpp
unpack.lo: msgpack/type/tuple.hpp msgpack/zone.hpp
zone.lo: msgpack/type/tuple.hpp msgpack/zone.hpp

msgpack/type/tuple.hpp: msgpack/type/tuple.hpp.erb
	$(ERB) $< > $@.tmp
	mv $@.tmp $@

msgpack/zone.hpp: msgpack/zone.hpp.erb
	$(ERB) $< > $@.tmp
	mv $@.tmp $@

MOSTLYCLEANFILES = \
		msgpack/type/tuple.hpp \
		msgpack/zone.hpp

# FIXME
libmsgpack_la_LDFLAGS = -version-info 0:0:0

