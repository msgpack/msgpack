#!/bin/sh

mkdir -p gem/ext
mkdir -p gem/msgpack
cp extconf.rb       gem/ext/
cp pack.c           gem/ext/
cp pack.h           gem/ext/
cp rbinit.c         gem/ext/
cp unpack.c         gem/ext/
cp unpack.h         gem/ext/
cat test_case.rb | sed "s/require ['\"]msgpack['\"]/require File.dirname(__FILE__) + '\/test_helper.rb'/" > gem/test/msgpack_test.rb
cp ../AUTHORS        gem/AUTHORS
cp ../ChangeLog      gem/ChangeLog
cp ../msgpack/pack_define.h     gem/msgpack/
cp ../msgpack/pack_template.h   gem/msgpack/
cp ../msgpack/unpack_define.h   gem/msgpack/
cp ../msgpack/unpack_template.h gem/msgpack/

cd gem && rake --trace package

