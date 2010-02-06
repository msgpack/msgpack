#!/bin/sh

mkdir -p ext
mkdir -p msgpack
cp extconf.rb   ext/
cp pack.c       ext/
cp pack.h       ext/
cp rbinit.c     ext/
cp unpack.c     ext/
cp unpack.h     ext/
cp ../AUTHORS   ./
cp ../ChangeLog ./
cp ../msgpack/pack_define.h     msgpack/
cp ../msgpack/pack_template.h   msgpack/
cp ../msgpack/unpack_define.h   msgpack/
cp ../msgpack/unpack_template.h msgpack/
cp ../msgpack/sysdep.h          msgpack/
cat msgpack_test.rb | sed "s/require ['\"]msgpack['\"]/require File.dirname(__FILE__) + '\/test_helper.rb'/" > test/msgpack_test.rb

gem build msgpack.gemspec

