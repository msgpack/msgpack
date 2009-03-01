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
	ruby/unpack.h

