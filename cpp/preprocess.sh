#!/bin/sh

preprocess() {
	ruby -r erb -e 'puts ERB.new(ARGF.read).result' $1.erb > $1.tmp
	if [ "$?" != 0 ]; then
		echo ""
		echo "** preprocess failed **"
		echo ""
	else
		mv $1.tmp $1
	fi
}

preprocess msgpack/type/tuple.hpp
preprocess msgpack/type/define.hpp
preprocess msgpack/zone.hpp

