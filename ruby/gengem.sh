#!/bin/sh

cp extconf.rb       gem/ext/
cp pack.c           gem/ext/
cp pack.h           gem/ext/
cp rbinit.c         gem/ext/
cp unpack.c         gem/ext/
cp unpack.h         gem/ext/
#cp ../README        gem/README.txt
cp ../msgpack/pack_template.h   gem/msgpack/
cp ../msgpack/unpack_define.h   gem/msgpack/
cp ../msgpack/unpack_template.h gem/msgpack/

cd gem && rake --trace package

