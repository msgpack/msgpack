MessagePack
===========
Extremely efficient object serialization library. It's like JSON, but very fast and small.


## What's MessagePack?

MessagePack is a binary-based efficient object serialization library. It enables to exchange structured objects between many languages like JSON. But unlike JSON, it is very fast and small.

Typical small integer (like flags or error code) is saved only in 1 byte, and typical short string only needs 1 byte except the length of the string itself. \[1,2,3\] (3 elements array) is serialized in 4 bytes using MessagePack as follows:

    require 'msgpack'
    msg = [1,2,3].to_msgpack  #=> "\x93\x01\x02\x03"
    MessagePack.unpack(msg)   #=> [1,2,3]


## Performance

![Serialization + Deserialization Speed Test](http://msgpack.org/index/speedtest.png)

In this test, it measured the elapsed time of serializing and deserializing 200,000 target objects. The target object consists of the three integers and 512 bytes string.
The source code of this test is available from [frsyuki' serializer-speed-test repository.](http://github.com/frsyuki/serializer-speed-test)


## Getting Started

Usage and other documents about implementations in each language are found at [the web site.](http://msgpack.org/)


## Learn More

  - [Project Web Site](http://msgpack.org/)
  - [MessagePack format specification](http://wiki.msgpack.org/display/MSGPACK/Format+specification)
  - [Repository at github](http://github.com/msgpack/msgpack)
  - [Wiki](http://wiki.msgpack.org/display/MSGPACK/Home)
  - [MessagePack-RPC](http://github.com/msgpack/msgpack-rpc)

