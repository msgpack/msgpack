#!/bin/sh

cp extconf.rb       gem/ext/
cp pack.c           gem/ext/
cp pack.h           gem/ext/
cp pack_inline.h    gem/ext/
cp rbinit.c         gem/ext/
cp unpack.c         gem/ext/
cp unpack.h         gem/ext/
cp unpack_context.h gem/ext/
cp unpack_inline.c  gem/ext/
cp ../README        gem/README.txt
cp ../msgpack/pack/inline_context.h    gem/msgpack/pack/
cp ../msgpack/pack/inline_impl.h       gem/msgpack/pack/
cp ../msgpack/unpack/inline_context.h  gem/msgpack/unpack/
cp ../msgpack/unpack/inline_impl.h     gem/msgpack/unpack/

cd gem && rake --trace package

