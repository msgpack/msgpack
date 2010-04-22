MessagePack for C/C++
=====================
Binary-based efficient object serialization library.


## Installation

Download latest package from [releases of MessagePack](http://sourceforge.net/projects/msgpack/files/) and extract it.

On UNIX-like platform, run ./configure && make && sudo make install:

    $ ./configure
    $ make
    $ sudo make install

On Windows, open msgpack_vc8.vcproj file and build it using batch build. DLLs are built on lib folder, and the headers are built on include folder.

To use the library in your program, include msgpack.hpp header and link msgpack and msgpackc library.


## Example

    #include <msgpack.hpp>
    #include <vector>
    
    int main(void) {
        // This is target object.
        std::vector<std::string> target;
        target.push_back("Hello,");
        target.push_back("World!");
    
        // Serialize it.
        msgpack::sbuffer buffer;  // simple buffer
        msgpack::pack(&buffer, target);
    
        // Deserialize the serialized data.
        msgpack::zone mempool;    // this manages the life of deserialized object
        msgpack::object obj;
        msgpack::unpack_return ret =
                msgpack::unpack(buffer.data, buffer.size, NULL, &mempool, &obj);
    
        if(ret != msgapck::UNPACK_SUCCESS) {
            // error check
            exit(1);
        }
    
        // Print the deserialized object to stdout.
        std::cout << obj << std::endl;    // ["Hello," "World!"]
    
        // Convert the deserialized object to staticaly typed object.
        std::vector<std::string> result;
        obj.convert(&result);
    
        // If the type is mismatched, it throws msgpack::type_error.
        obj.as<int>();  // type is mismatched, msgpack::type_error is thrown
    }

API document and other example codes are available at the [wiki.](http://msgpack.sourceforge.net/start)


## License

Copyright (C) 2008-2010 FURUHASHI Sadayuki

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

See also NOTICE file.

