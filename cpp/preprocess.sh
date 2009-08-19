#!/bin/sh

function preprocess() {
	erb $1.erb > $1.tmp
	mv $1.tmp $1
}

preprocess msgpack/type/tuple.hpp
preprocess msgpack/type/define.hpp
preprocess msgpack/zone.hpp

