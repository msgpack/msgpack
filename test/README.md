MessagePack cross-language test cases
=====================================

## cases

Valid serialized data are stored in "cases.mpac" and "cases_compact.mpac".
These files describe same objects. And "cases.json" describes an array of the described objects.

Thus you can verify your implementations as comparing the objects.


## crosslang

The *crosslang* tool reads serialized data from stdin and writes re-serialize data to stdout.

There are C++ and Ruby implementation of crosslang tool. You can verify your implementation
as comparing that implementations.

### C++ version

    $ cd ../cpp && ./configure && make && make install
    or
    $ port install msgpack  # MacPorts
    
    $ g++ -Wall -lmsgpack crosslang.cc

    Usage: ./crosslang [in-file] [out-file]
    
    This tool is for testing of MessagePack implementation.
    This does following behavior:
    
      1. Reads objects serialized by MessagePack from <in-file> (default: stdin)
      2. Re-serializes the objects using C++ implementation of MessagePack (Note that C++ implementation is considered valid)
      3. Writes the re-serialized objects into <out-file> (default: stdout)

### Ruby version

    $ gem install msgpack
    or
    $ port install rb_msgpack   # MacPorts

    $ ruby crosslang.rb
    Usage: crosslang.rb [in-file] [out-file]
    
    This tool is for testing of MessagePack implementation.
    This does following behavior:
    
      1. Reads objects serialized by MessagePack from <in-file> (default: stdin)
      2. Re-serializes the objects using Ruby implementation of MessagePack (Note that Ruby implementation is considered valid)
      3. Writes the re-serialized objects into <out-file> (default: stdout)

