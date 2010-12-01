#!/bin/sh

mkdir -p ext
mkdir -p msgpack
cp extconf.rb   ext/
cp pack.c       ext/
cp pack.h       ext/
cp rbinit.c     ext/
cp unpack.c     ext/
cp unpack.h     ext/
cp compat.h     ext/
cp version.rb   ext/
cp ../msgpack/pack_define.h     msgpack/
cp ../msgpack/pack_template.h   msgpack/
cp ../msgpack/unpack_define.h   msgpack/
cp ../msgpack/unpack_template.h msgpack/
cp ../msgpack/sysdep.h          msgpack/
cp ../test/cases.mpac           test/
cp ../test/cases_compact.mpac   test/
cp ../test/cases.json           test/

gem build msgpack.gemspec

rdoc rbinit.c pack.c unpack.c

if [ $? -eq 0 ]; then
	rm -rf ext msgpack test/msgpack_test.rb
fi

# gem install gem-compile                     # on msys
# gem compile msgpack-$version.gem            # on msys
# gem compile msgpack-$version.gem -p mswin32 # on msys
# gem push msgpack-$version.gem
# gem push msgpack-$version-x86-mingw32.gem
# gem push msgpack-$version-mswin32.gem

