IF NOT EXIST include                  MKDIR include
IF NOT EXIST include\msgpack          MKDIR include\msgpack
IF NOT EXIST include\msgpack\type     MKDIR include\msgpack\type
IF NOT EXIST include\msgpack\type\tr1 MKDIR include\msgpack\type\tr1
copy msgpack\pack_define.h      include\msgpack\
copy msgpack\pack_template.h    include\msgpack\
copy msgpack\unpack_define.h    include\msgpack\
copy msgpack\unpack_template.h  include\msgpack\
copy msgpack\sysdep.h           include\msgpack\
copy msgpack.h                     include\
copy msgpack\sbuffer.h             include\msgpack\
copy msgpack\vrefbuffer.h          include\msgpack\
copy msgpack\zbuffer.h             include\msgpack\
copy msgpack\pack.h                include\msgpack\
copy msgpack\unpack.h              include\msgpack\
copy msgpack\object.h              include\msgpack\
copy msgpack\zone.h                include\msgpack\
copy msgpack.hpp                   include\
copy msgpack\sbuffer.hpp           include\msgpack\
copy msgpack\vrefbuffer.hpp        include\msgpack\
copy msgpack\zbuffer.hpp           include\msgpack\
copy msgpack\pack.hpp              include\msgpack\
copy msgpack\unpack.hpp            include\msgpack\
copy msgpack\object.hpp            include\msgpack\
copy msgpack\zone.hpp              include\msgpack\
copy msgpack\type.hpp              include\msgpack\type\
copy msgpack\type\bool.hpp         include\msgpack\type\
copy msgpack\type\float.hpp        include\msgpack\type\
copy msgpack\type\int.hpp          include\msgpack\type\
copy msgpack\type\list.hpp         include\msgpack\type\
copy msgpack\type\deque.hpp        include\msgpack\type\
copy msgpack\type\map.hpp          include\msgpack\type\
copy msgpack\type\nil.hpp          include\msgpack\type\
copy msgpack\type\pair.hpp         include\msgpack\type\
copy msgpack\type\raw.hpp          include\msgpack\type\
copy msgpack\type\set.hpp          include\msgpack\type\
copy msgpack\type\string.hpp       include\msgpack\type\
copy msgpack\type\vector.hpp       include\msgpack\type\
copy msgpack\type\tuple.hpp        include\msgpack\type\
copy msgpack\type\define.hpp       include\msgpack\type\
copy msgpack\type\tr1\unordered_map.hpp  include\msgpack\type\
copy msgpack\type\tr1\unordered_set.hpp  include\msgpack\type\

