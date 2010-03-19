IF NOT EXIST include                  MKDIR include
IF NOT EXIST include\msgpack          MKDIR include\msgpack
IF NOT EXIST include\msgpack\type     MKDIR include\msgpack\type
IF NOT EXIST include\msgpack\type\tr1 MKDIR include\msgpack\type\tr1
copy msgpack\pack_define.h         include\msgpack\
copy msgpack\pack_template.h       include\msgpack\
copy msgpack\unpack_define.h       include\msgpack\
copy msgpack\unpack_template.h     include\msgpack\
copy msgpack\sysdep.h              include\msgpack\
copy c\msgpack.h                   include\
copy c\msgpack\sbuffer.h           include\msgpack\
copy c\msgpack\vrefbuffer.h        include\msgpack\
copy c\msgpack\pack.h              include\msgpack\
copy c\msgpack\unpack.h            include\msgpack\
copy c\msgpack\object.h            include\msgpack\
copy c\msgpack\zone.h              include\msgpack\
copy cpp\msgpack.hpp               include\
copy cpp\msgpack\sbuffer.hpp       include\msgpack\
copy cpp\msgpack\vrefbuffer.hpp    include\msgpack\
copy cpp\msgpack\pack.hpp          include\msgpack\
copy cpp\msgpack\unpack.hpp        include\msgpack\
copy cpp\msgpack\object.hpp        include\msgpack\
copy cpp\msgpack\zone.hpp          include\msgpack\
copy cpp\msgpack\type.hpp          include\msgpack\type\
copy cpp\msgpack\type\bool.hpp     include\msgpack\type\
copy cpp\msgpack\type\float.hpp    include\msgpack\type\
copy cpp\msgpack\type\int.hpp      include\msgpack\type\
copy cpp\msgpack\type\list.hpp     include\msgpack\type\
copy cpp\msgpack\type\deque.hpp    include\msgpack\type\
copy cpp\msgpack\type\map.hpp      include\msgpack\type\
copy cpp\msgpack\type\nil.hpp      include\msgpack\type\
copy cpp\msgpack\type\pair.hpp     include\msgpack\type\
copy cpp\msgpack\type\raw.hpp      include\msgpack\type\
copy cpp\msgpack\type\set.hpp      include\msgpack\type\
copy cpp\msgpack\type\string.hpp   include\msgpack\type\
copy cpp\msgpack\type\vector.hpp   include\msgpack\type\
copy cpp\msgpack\type\tuple.hpp    include\msgpack\type\
copy cpp\msgpack\type\define.hpp   include\msgpack\type\
copy cpp\msgpack\type\tr1\unordered_map.hpp  include\msgpack\type\
copy cpp\msgpack\type\tr1\unordered_set.hpp  include\msgpack\type\

