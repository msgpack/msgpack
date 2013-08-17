# MessagePack format specification

**This spec is updated. See [spec.md](spec.md) for the updated version.**


MessagePack saves type-information to the serialized data. Thus each data is stored in **type-data** or **type-length-data** style.
MessagePack supports following types:

* Fixed length types
  * Integers
  * nil
  * boolean
  * Floating point
* Variable length types
  * Raw bytes
* Container types
  * Arrays
  * Maps

Each type has one or more serialize format:

* Fixed length types
  * Integers
      * positive fixnum
      * negative fixnum
      * uint 8
      * uint 16
      * uint 32
      * uint 64
      * int 8
      * int 16
      * int 32
      * int 64
  * Nil
      * nil
  * Boolean
      * true
      * false
  * Floating point
      * float
      * double
* Variable length types
  * Raw bytes
      * fix raw
      * raw 16
      * raw 32
* Container types
  * Arrays
      * fix array
      * array 16
      * array 32
  * Maps
      * fix map
      * map 16
      * map 32

To serialize strings, use UTF-8 encoding and Raw type.

See this thread to understand the reason why msgpack doesn't have string type:&nbsp;[https://github.com/msgpack/msgpack/issues/121]

## Integers

### positive fixnum

save an integer within the range [0, 127] in 1 bytes.

    +--------+
    |0XXXXXXX|
    +--------+
    => unsigned 8-bit 0XXXXXXX


### negative fixnum

save an integer within the range [-32, -1] in 1 bytes.

    +--------+
    |111XXXXX|
    +--------+
    => signed 8-bit 111XXXXX


### uint 8

save an unsigned 8-bit integer in 2 bytes.

    +--------+--------+
    |  0xcc  |XXXXXXXX|
    +--------+--------+
    => unsigned 8-bit XXXXXXXX


### uint 16

save an unsigned 16-bit big-endian integer in 3 bytes.

    +--------+--------+--------+
    |  0xcd  |XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+
    => unsigned 16-bit big-endian XXXXXXXX_XXXXXXXX


### uint 32

save an unsigned 32-bit big-endian integer in 5 bytes.

    +--------+--------+--------+--------+--------+
    |  0xce  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+--------+--------+
    => unsigned 32-bit big-endian XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX


### uint 64

save an unsigned 64-bit big-endian integer in 9 bytes.

    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xcf  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    => unsigned 64-bit big-endian XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX


### int 8

save a signed 8-bit integer in 2 bytes.

    +--------+--------+
    |  0xd0  |XXXXXXXX|
    +--------+--------+
    => signed 8-bit XXXXXXXX

### int 16

save a signed 16-bit big-endian integer in 3 bytes.

    +--------+--------+--------+
    |  0xd1  |XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+
    => signed 16-bit big-endian XXXXXXXX_XXXXXXXX


### int 32

save a signed 32-bit big-endian integer in 5 bytes.

    +--------+--------+--------+--------+--------+
    |  0xd2  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+--------+--------+
    => signed 32-bit big-endian XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX

### int 64

save a signed 64-bit big-endian integer in 9 bytes.

    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd3  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    => signed 64-bit big-endian XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX


## Nil


### nil

save a nil.

    +--------+
    |  0xc0  |
    +--------+


## Boolean


### true

save a true.

    +--------+
    |  0xc3  |
    +--------+


### false

save a false.

    +--------+
    |  0xc2  |
    +--------+


## Floating point


### float

save a big-endian IEEE 754 single precision floating point number in 5 bytes.

    +--------+--------+--------+--------+--------+
    |  0xca  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+--------+--------+
    => big-endian IEEE 754 single precision floating point number XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX


### double

save a big-endian IEEE 754 double precision floating point number in 9 bytes.

    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xcb  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    => big-endian IEEE 754 single precision floating point number XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX


## Raw bytes


### fix raw

save raw bytes up to 31 bytes.

    +--------+--------
    |101XXXXX|...N bytes
    +--------+--------
    => 000XXXXXX (=N) bytes of raw bytes.


### raw 16

save raw bytes up to (2^16)-1 bytes. Length is stored in unsigned 16-bit big-endian integer.

    +--------+--------+--------+--------
    |  0xda  |XXXXXXXX|XXXXXXXX|...N bytes
    +--------+--------+--------+--------
    => XXXXXXXX_XXXXXXXX (=N) bytes of raw bytes.


### raw 32

save raw bytes up to (2^32)-1 bytes. Length is stored in unsigned 32-bit big-endian integer.

    +--------+--------+--------+--------+--------+--------
    |  0xdb  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|...N bytes
    +--------+--------+--------+--------+--------+--------
    => XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX (=N) bytes of raw bytes.



## Arrays


### fix array

save an array up to 15 elements.

    +--------+--------
    |1001XXXX|...N objects
    +--------+--------
    => 0000XXXX (=N) elements array.


### array 16

save an array up to (2^16)-1 elements. Number of elements is stored in unsigned 16-bit big-endian integer.

    +--------+--------+--------+--------
    |  0xdc  |XXXXXXXX|XXXXXXXX|...N objects
    +--------+--------+--------+--------
    => XXXXXXXX_XXXXXXXX (=N) elements array.


### array 32

save an array up to (2^32)-1 elements. Number of elements is stored in unsigned 32-bit big-endian integer.

    +--------+--------+--------+--------+--------+--------
    |  0xdd  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|...N objects
    +--------+--------+--------+--------+--------+--------
    => XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX (=N) elements array.


## Maps


### fix map

save a map up to 15 elements.

    +--------+--------
    |1000XXXX|...N*2 objects
    +--------+--------
    => 0000XXXX (=N) elements map
       where odd elements are key and next element of the key is its associate value.


### map 16

save a map up to (2^16)-1 elements. Number of elements is stored in unsigned 16-bit big-endian integer.

    +--------+--------+--------+--------
    |  0xde  |XXXXXXXX|XXXXXXXX|...N*2 objects
    +--------+--------+--------+--------
    => XXXXXXXX_XXXXXXXX (=N) elements map
       where odd elements are key and next element of the key is its associate value.


### map 32

save a map up to (2^32)-1 elements. Number of elements is stored in unsigned 32-bit big-endian integer.

    +--------+--------+--------+--------+--------+--------
    |  0xdf  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|...N*2 objects
    +--------+--------+--------+--------+--------+--------
    => XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX (=N) elements map
       where odd elements are key and next element of the key is its associate value.



## Type Chart

<table>
<tr><th>Type</th><th>Binary</th><th>Hex</th></tr>
<tr><td>Positive FixNum</td><td>0xxxxxxx</td><td>0x00 - 0x7f</td></tr>
<tr><td>FixMap</td><td>1000xxxx</td><td>0x80 - 0x8f</td></tr>
<tr><td>FixArray</td><td>1001xxxx</td><td>0x90 - 0x9f</td></tr>
<tr><td>FixRaw</td><td>101xxxxx</td><td>0xa0 - 0xbf</td></tr>
<tr><td>nil</td><td>11000000</td><td>0xc0</td></tr>
<tr><td>_reserved_</td><td>11000001</td><td>0xc1</td></tr>
<tr><td>false</td><td>11000010</td><td>0xc2</td></tr>
<tr><td>true</td><td>11000011</td><td>0xc3</td></tr>
<tr><td>_reserved_</td><td>11000100</td><td>0xc4</td></tr>
<tr><td>_reserved_</td><td>11000101</td><td>0xc5</td></tr>
<tr><td>_reserved_</td><td>11000110</td><td>0xc6</td></tr>
<tr><td>_reserved_</td><td>11000111</td><td>0xc7</td></tr>
<tr><td>_reserved_</td><td>11001000</td><td>0xc8</td></tr>
<tr><td>_reserved_</td><td>11001001</td><td>0xc9</td></tr>
<tr><td>float</td><td>11001010</td><td>0xca</td></tr>
<tr><td>double</td><td>11001011</td><td>0xcb</td></tr>
<tr><td>uint 8</td><td>11001100</td><td>0xcc</td></tr>
<tr><td>uint 16</td><td>11001101</td><td>0xcd</td></tr>
<tr><td>uint 32</td><td>11001110</td><td>0xce</td></tr>
<tr><td>uint 64</td><td>11001111</td><td>0xcf</td></tr>
<tr><td>int 8</td><td>11010000</td><td>0xd0</td></tr>
<tr><td>int 16</td><td>11010001</td><td>0xd1</td></tr>
<tr><td>int 32</td><td>11010010</td><td>0xd2</td></tr>
<tr><td>int 64</td><td>11010011</td><td>0xd3</td></tr>
<tr><td>_reserved_</td><td>11010100</td><td>0xd4</td></tr>
<tr><td>_reserved_</td><td>11010101</td><td>0xd5</td></tr>
<tr><td>_reserved_</td><td>11010110</td><td>0xd6</td></tr>
<tr><td>_reserved_</td><td>11010111</td><td>0xd7</td></tr>
<tr><td>_reserved_</td><td>11011000</td><td>0xd8</td></tr>
<tr><td>_reserved_</td><td>11011001</td><td>0xd9</td></tr>
<tr><td>raw 16</td><td>11011010</td><td>0xda</td></tr>
<tr><td>raw 32</td><td>11011011</td><td>0xdb</td></tr>
<tr><td>array 16</td><td>11011100</td><td>0xdc</td></tr>
<tr><td>array 32</td><td>11011101</td><td>0xdd</td></tr>
<tr><td>map 16</td><td>11011110</td><td>0xde</td></tr>
<tr><td>map 32</td><td>11011111</td><td>0xdf</td></tr>
<tr><td>Negative FixNum</td><td>111xxxxx</td><td>0xe0 - 0xff</td></tr>


