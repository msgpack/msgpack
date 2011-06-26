MessagePack
===========
Extremely efficient object serialization library. It's like JSON, but very fast and small.


## What's MessagePack?

**MessagePack** is a binary-based efficient object serialization library. It enables to exchange structured objects between many languages like JSON. But unlike JSON, it is very fast and small.

Typical small integer (like flags or error code) is saved only in 1 byte, and typical short string only needs 1 byte except the length of the string itself. \[1,2,3\] (3 elements array) is serialized in 4 bytes using MessagePack as follows:

    require 'msgpack'
    msg = [1,2,3].to_msgpack  #=> "\x93\x01\x02\x03"
    MessagePack.unpack(msg)   #=> [1,2,3]

**MessagePack-RPC** is cross-language RPC library for client, server and cluster applications. Because it releases you from complicated network programming completely and provides well-designed API, you can easily implement advanced network applications with MessagePack-RPC.

    require 'msgpack/rpc'
    class MyHandler
      def add(x,y) return x+y end
    end
    svr = MessagePack::RPC::Server.new
    svr.listen('0.0.0.0', 18800, MyHandler.new)
    svr.run

    require 'msgpack/rpc'
    c = MessagePack::RPC::Client.new('127.0.0.1',18800)
    result = c.call(:add, 1, 2)  #=> 3


## Getting Started

Usage and other documents about implementations in each language are found at [the web site.](http://msgpack.org/)


## Learn More

  - [Web Site](http://msgpack.org/)
  - [Wiki](http://wiki.msgpack.org/display/MSGPACK/Home)
  - [Issues](http://jira.msgpack.org/browse/MSGPACK)
  - [Sources](https://github.com/msgpack)

