MessagePack
===========

MessagePack is an efficient binary serialization format. It's like JSON. but fast and small.

This repository manages specification of MessagePack format. See [Spec](spec.md) for the specification.

Implementation projects have each own repository. See [msgpack.org](http://msgpack.org/) website to find implementations and their documents.

If you'd like to show your msgpack implementation to the [msgpack.org](http://msgpack.org/) website, please follow the [website document](https://github.com/msgpack/website).

## How to create html with table of content

first, install tocmd gem

	gem install redcarpet
	gem install pygments.rb
	gem install tocmd

then execute the following command:

	./build.sh
	
and the dist file in preview/spec.html