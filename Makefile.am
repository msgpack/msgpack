if ENABLE_CXX
export ERB
SUBDIRS = c cpp
else
SUBDIRS = c
endif

nobase_include_HEADERS = \
		msgpack/pack_define.h \
		msgpack/pack_template.h \
		msgpack/unpack_define.h \
		msgpack/unpack_template.h

EXTRA_DIST = \
	ruby/bench.rb \
	ruby/extconf.rb \
	ruby/gem/README \
	ruby/gem/Rakefile \
	ruby/gem/test/test_helper.rb \
	ruby/gengem.sh \
	ruby/msgpack.gemspec \
	ruby/pack.c \
	ruby/pack.h \
	ruby/rbinit.c \
	ruby/test_case.rb \
	ruby/test_format.rb \
	ruby/test_pack.rb \
	ruby/unpack.c \
	ruby/unpack.h \
	perl/Makefile.PL \
	perl/MessagePack.c \
	perl/benchmark/deserialize.pl \
	perl/benchmark/serialize.pl \
	perl/lib/Data/MessagePack.pm \
	perl/lib/Data/MessagePack \
	perl/lib/Data/MessagePack/Unpacker.pod \
	perl/pack.c \
	perl/ppport.h \
	perl/t/00_compile.t \
	perl/t/01_pack.t \
	perl/t/02_unpack.t \
	perl/t/03_stream_unpack.t \
	perl/t/04_invert.t \
	perl/t/Util.pm \
	perl/t/data.pl \
	perl/unpack.c \
	perl/xt/99_pod.t

