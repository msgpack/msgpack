# MessagePack specification

MessagePack is an object serialization specification like JSON.

MessagePack has two concepts: **type system** and **formats**.

Serialization is conversion from application objects into MessagePack formats via MessagePack type system.

Deserialization is conversion from MessagePack formats into application objects via MessagePack type system.

    Serialization:
        Application objects
        -->  MessagePack type system
        -->  MessagePack formats (byte array)

    Deserialization:
        MessagePack formats (byte array)
        -->  MessagePack type system
        -->  Application objects

This document describes the MessagePack type system, MessagePack formats and conversion of them.

## Table of contents

* MessagePack specification
  * [Type system](#type-system)
      * [Limitation](#limitation)
      * [Extension types](#extension-types)
  * [Formats](#formats)
      * [Overview](#overview)
      * [Notation in diagrams](#notation-in-diagrams)
      * [nil format](#nil-format)
      * [bool format family](#bool-format-family)
      * [int format family](#int-format-family)
      * [float format family](#float-format-family)
      * [str format family](#str-format-family)
      * [bin format family](#bin-format-family)
      * [array format family](#array-format-family)
      * [map format family](#map-format-family)
      * [ext format family](#ext-format-family)
      * [Timestamp extension type](#timestamp-extension-type)
  * [Serialization: type to format conversion](#serialization-type-to-format-conversion)
  * [Deserialization: format to type conversion](#deserialization-format-to-type-conversion)
  * [Future discussion](#future-discussion)
    * [Profile](#profile)
  * [Implementation guidelines](#implementation-guidelines)
    * [Upgrading MessagePack specification](#upgrading-messagepack-specification)

## Type system

* Types
  * **Integer** represents an integer
  * **Nil** represents nil
  * **Boolean** represents true or false
  * **Float** represents a IEEE 754 double precision floating point number including NaN and Infinity
  * **Raw**
      * **String** extending Raw type represents a UTF-8 string
      * **Binary** extending Raw type represents a byte array
  * **Array** represents a sequence of objects
  * **Map** represents key-value pairs of objects
  * **Extension** represents a tuple of type information and a byte array where type information is an integer whose meaning is defined by applications or MessagePack specification
      * **Timestamp** represents an instantaneous point on the time-line in the world that is independent from time zones or calendars. Maximum precision is nanoseconds.

### Limitation

* a value of an Integer object is limited from `-(2^63)` upto `(2^64)-1`
* maximum length of a Binary object is `(2^32)-1`
* maximum byte size of a String object is `(2^32)-1`
* String objects may contain invalid byte sequence and the behavior of a deserializer depends on the actual implementation when it received invalid byte sequence
    * Deserializers should provide functionality to get the original byte array so that applications can decide how to handle the object
* maximum number of elements of an Array object is `(2^32)-1`
* maximum number of key-value associations of a Map object is `(2^32)-1`

### Extension types

MessagePack allows applications to define application-specific types using the Extension type.
Extension type consists of an integer and a byte array where the integer represents a kind of types and the byte array represents data.

Applications can assign `0` to `127` to store application-specific type information. An example usage is that application defines `type = 0` as the application's unique type system, and stores name of a type and values of the type at the payload.

MessagePack reserves `-1` to `-128` for future extension to add predefined types. These types will be added to exchange more types without using pre-shared statically-typed schema across different programming environments.

    [0, 127]: application-specific types
    [-128, -1]: reserved for predefined types

Because extension types are intended to be added, old applications may not implement all of them. However, they can still handle such type as one of Extension types. Therefore, applications can decide whether they reject unknown Extension types, accept as opaque data, or transfer to another application without touching payload of them.

Here is the list of predefined extension types. Formats of the types are defined at [Formats](#formats-timestamp) section.

<table>
  <tr><th>Name</th><th>Type</th></tr>
  <tr><td>Timestamp</td><td>-1</td></tr>
  <tr><td>Bigint</td><td>-2</td></tr>
  <tr><td>Bigfloat</td><td>-3</td></tr>
  <tr><td>Bigdecimal (decimal encoded)</td><td>-4</td></tr>
  <tr><td>Bigdecimal (binary encoded)</td><td>-5</td></tr>
  <tr><td>Fractions</td><td>-6</td></tr>
</table>

## Formats

### Overview

<table>
  <tr><th>format name</th><th>first byte (in binary)</th><th>first byte (in hex)</th></th></tr>
  <tr><td>positive fixint</td><td>0xxxxxxx</td><td>0x00 - 0x7f</td></tr>
  <tr><td>fixmap</td><td>1000xxxx</td><td>0x80 - 0x8f</td></tr>
  <tr><td>fixarray</td><td>1001xxxx</td><td>0x90 - 0x9f</td></tr>
  <tr><td>fixstr</td><td>101xxxxx</td><td>0xa0 - 0xbf</td></tr>
  <tr><td>nil</td><td>11000000</td><td>0xc0</td></tr>
  <tr><td>(never used)</td><td>11000001</td><td>0xc1</td></tr>
  <tr><td>false</td><td>11000010</td><td>0xc2</td></tr>
  <tr><td>true</td><td>11000011</td><td>0xc3</td></tr>
  <tr><td>bin 8</td><td>11000100</td><td>0xc4</td></tr>
  <tr><td>bin 16</td><td>11000101</td><td>0xc5</td></tr>
  <tr><td>bin 32</td><td>11000110</td><td>0xc6</td></tr>
  <tr><td>ext 8</td><td>11000111</td><td>0xc7</td></tr>
  <tr><td>ext 16</td><td>11001000</td><td>0xc8</td></tr>
  <tr><td>ext 32</td><td>11001001</td><td>0xc9</td></tr>
  <tr><td>float 32</td><td>11001010</td><td>0xca</td></tr>
  <tr><td>float 64</td><td>11001011</td><td>0xcb</td></tr>
  <tr><td>uint 8</td><td>11001100</td><td>0xcc</td></tr>
  <tr><td>uint 16</td><td>11001101</td><td>0xcd</td></tr>
  <tr><td>uint 32</td><td>11001110</td><td>0xce</td></tr>
  <tr><td>uint 64</td><td>11001111</td><td>0xcf</td></tr>
  <tr><td>int 8</td><td>11010000</td><td>0xd0</td></tr>
  <tr><td>int 16</td><td>11010001</td><td>0xd1</td></tr>
  <tr><td>int 32</td><td>11010010</td><td>0xd2</td></tr>
  <tr><td>int 64</td><td>11010011</td><td>0xd3</td></tr>
  <tr><td>fixext 1</td><td>11010100</td><td>0xd4</td></tr>
  <tr><td>fixext 2</td><td>11010101</td><td>0xd5</td></tr>
  <tr><td>fixext 4</td><td>11010110</td><td>0xd6</td></tr>
  <tr><td>fixext 8</td><td>11010111</td><td>0xd7</td></tr>
  <tr><td>fixext 16</td><td>11011000</td><td>0xd8</td></tr>
  <tr><td>str 8</td><td>11011001</td><td>0xd9</td></tr>
  <tr><td>str 16</td><td>11011010</td><td>0xda</td></tr>
  <tr><td>str 32</td><td>11011011</td><td>0xdb</td></tr>
  <tr><td>array 16</td><td>11011100</td><td>0xdc</td></tr>
  <tr><td>array 32</td><td>11011101</td><td>0xdd</td></tr>
  <tr><td>map 16</td><td>11011110</td><td>0xde</td></tr>
  <tr><td>map 32</td><td>11011111</td><td>0xdf</td></tr>
  <tr><td>negative fixint</td><td>111xxxxx</td><td>0xe0 - 0xff</td></tr>
</table>

### Notation in diagrams

    one byte:
    +--------+
    |        |
    +--------+

    a variable number of bytes:
    +========+
    |        |
    +========+

    variable number of objects stored in MessagePack format:
    +~~~~~~~~~~~~~~~~~+
    |                 |
    +~~~~~~~~~~~~~~~~~+

`X`, `Y`, `Z` and `A` are the symbols that will be replaced by an actual bit.

### nil format

Nil format stores nil in 1 byte.

    nil:
    +--------+
    |  0xc0  |
    +--------+

### bool format family

Bool format family stores false or true in 1 byte.

    false:
    +--------+
    |  0xc2  |
    +--------+

    true:
    +--------+
    |  0xc3  |
    +--------+

### int format family

Int format family stores an integer in 1, 2, 3, 5, or 9 bytes.

    positive fixnum stores 7-bit positive integer
    +--------+
    |0XXXXXXX|
    +--------+

    negative fixnum stores 5-bit negative integer
    +--------+
    |111YYYYY|
    +--------+

    * 0XXXXXXX is 8-bit unsigned integer
    * 111YYYYY is 8-bit signed integer

    uint 8 stores a 8-bit unsigned integer
    +--------+--------+
    |  0xcc  |ZZZZZZZZ|
    +--------+--------+

    uint 16 stores a 16-bit big-endian unsigned integer
    +--------+--------+--------+
    |  0xcd  |ZZZZZZZZ|ZZZZZZZZ|
    +--------+--------+--------+

    uint 32 stores a 32-bit big-endian unsigned integer
    +--------+--------+--------+--------+--------+
    |  0xce  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|
    +--------+--------+--------+--------+--------+

    uint 64 stores a 64-bit big-endian unsigned integer
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xcf  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+

    int 8 stores a 8-bit signed integer
    +--------+--------+
    |  0xd0  |ZZZZZZZZ|
    +--------+--------+

    int 16 stores a 16-bit big-endian signed integer
    +--------+--------+--------+
    |  0xd1  |ZZZZZZZZ|ZZZZZZZZ|
    +--------+--------+--------+

    int 32 stores a 32-bit big-endian signed integer
    +--------+--------+--------+--------+--------+
    |  0xd2  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|
    +--------+--------+--------+--------+--------+

    int 64 stores a 64-bit big-endian signed integer
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd3  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+

### float format family

Float format family stores a floating point number in 5 bytes or 9 bytes.

    float 32 stores a floating point number in IEEE 754 single precision floating point number format:
    +--------+--------+--------+--------+--------+
    |  0xca  |XXXXXXXX|XXXXXXXX|XXXXXXXX|XXXXXXXX|
    +--------+--------+--------+--------+--------+

    float 64 stores a floating point number in IEEE 754 double precision floating point number format:
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xcb  |YYYYYYYY|YYYYYYYY|YYYYYYYY|YYYYYYYY|YYYYYYYY|YYYYYYYY|YYYYYYYY|YYYYYYYY|
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+

    where
    * XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX is a big-endian IEEE 754 single precision floating point number.
      Extension of precision from single-precision to double-precision does not lose precision.
    * YYYYYYYY_YYYYYYYY_YYYYYYYY_YYYYYYYY_YYYYYYYY_YYYYYYYY_YYYYYYYY_YYYYYYYY is a big-endian
      IEEE 754 double precision floating point number

### str format family

Str format family stores a byte array in 1, 2, 3, or 5 bytes of extra bytes in addition to the size of the byte array.

    fixstr stores a byte array whose length is upto 31 bytes:
    +--------+========+
    |101XXXXX|  data  |
    +--------+========+

    str 8 stores a byte array whose length is upto (2^8)-1 bytes:
    +--------+--------+========+
    |  0xd9  |YYYYYYYY|  data  |
    +--------+--------+========+

    str 16 stores a byte array whose length is upto (2^16)-1 bytes:
    +--------+--------+--------+========+
    |  0xda  |ZZZZZZZZ|ZZZZZZZZ|  data  |
    +--------+--------+--------+========+

    str 32 stores a byte array whose length is upto (2^32)-1 bytes:
    +--------+--------+--------+--------+--------+========+
    |  0xdb  |AAAAAAAA|AAAAAAAA|AAAAAAAA|AAAAAAAA|  data  |
    +--------+--------+--------+--------+--------+========+

    where
    * XXXXX is a 5-bit unsigned integer which represents N
    * YYYYYYYY is a 8-bit unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ is a 16-bit big-endian unsigned integer which represents N
    * AAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA is a 32-bit big-endian unsigned integer which represents N
    * N is the length of data

### bin format family

Bin format family stores an byte array in 2, 3, or 5 bytes of extra bytes in addition to the size of the byte array.

    bin 8 stores a byte array whose length is upto (2^8)-1 bytes:
    +--------+--------+========+
    |  0xc4  |XXXXXXXX|  data  |
    +--------+--------+========+

    bin 16 stores a byte array whose length is upto (2^16)-1 bytes:
    +--------+--------+--------+========+
    |  0xc5  |YYYYYYYY|YYYYYYYY|  data  |
    +--------+--------+--------+========+

    bin 32 stores a byte array whose length is upto (2^32)-1 bytes:
    +--------+--------+--------+--------+--------+========+
    |  0xc6  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|  data  |
    +--------+--------+--------+--------+--------+========+

    where
    * XXXXXXXX is a 8-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a 32-bit big-endian unsigned integer which represents N
    * N is the length of data

### array format family

Array format family stores a sequence of elements in 1, 3, or 5 bytes of extra bytes in addition to the elements.

    fixarray stores an array whose length is upto 15 elements:
    +--------+~~~~~~~~~~~~~~~~~+
    |1001XXXX|    N objects    |
    +--------+~~~~~~~~~~~~~~~~~+

    array 16 stores an array whose length is upto (2^16)-1 elements:
    +--------+--------+--------+~~~~~~~~~~~~~~~~~+
    |  0xdc  |YYYYYYYY|YYYYYYYY|    N objects    |
    +--------+--------+--------+~~~~~~~~~~~~~~~~~+

    array 32 stores an array whose length is upto (2^32)-1 elements:
    +--------+--------+--------+--------+--------+~~~~~~~~~~~~~~~~~+
    |  0xdd  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|    N objects    |
    +--------+--------+--------+--------+--------+~~~~~~~~~~~~~~~~~+

    where
    * XXXX is a 4-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a 32-bit big-endian unsigned integer which represents N
        N is the size of a array

### map format family

Map format family stores a sequence of key-value pairs in 1, 3, or 5 bytes of extra bytes in addition to the key-value pairs.

    fixmap stores a map whose length is upto 15 elements
    +--------+~~~~~~~~~~~~~~~~~+
    |1000XXXX|   N*2 objects   |
    +--------+~~~~~~~~~~~~~~~~~+

    map 16 stores a map whose length is upto (2^16)-1 elements
    +--------+--------+--------+~~~~~~~~~~~~~~~~~+
    |  0xde  |YYYYYYYY|YYYYYYYY|   N*2 objects   |
    +--------+--------+--------+~~~~~~~~~~~~~~~~~+

    map 32 stores a map whose length is upto (2^32)-1 elements
    +--------+--------+--------+--------+--------+~~~~~~~~~~~~~~~~~+
    |  0xdf  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|   N*2 objects   |
    +--------+--------+--------+--------+--------+~~~~~~~~~~~~~~~~~+

    where
    * XXXX is a 4-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a 32-bit big-endian unsigned integer which represents N
    * N is the size of a map
    * odd elements in objects are keys of a map
    * the next element of a key is its associated value

### ext format family

Ext format family stores a tuple of an integer and a byte array.

    fixext 1 stores an integer and a byte array whose length is 1 byte
    +--------+--------+--------+
    |  0xd4  |  type  |  data  |
    +--------+--------+--------+

    fixext 2 stores an integer and a byte array whose length is 2 bytes
    +--------+--------+--------+--------+
    |  0xd5  |  type  |       data      |
    +--------+--------+--------+--------+

    fixext 4 stores an integer and a byte array whose length is 4 bytes
    +--------+--------+--------+--------+--------+--------+
    |  0xd6  |  type  |                data               |
    +--------+--------+--------+--------+--------+--------+

    fixext 8 stores an integer and a byte array whose length is 8 bytes
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd7  |  type  |                                  data                                 |
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+

    fixext 16 stores an integer and a byte array whose length is 16 bytes
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd8  |  type  |                                  data                                  
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    +--------+--------+--------+--------+--------+--------+--------+--------+
                                  data (cont.)                              |
    +--------+--------+--------+--------+--------+--------+--------+--------+

    ext 8 stores an integer and a byte array whose length is upto (2^8)-1 bytes:
    +--------+--------+--------+========+
    |  0xc7  |XXXXXXXX|  type  |  data  |
    +--------+--------+--------+========+

    ext 16 stores an integer and a byte array whose length is upto (2^16)-1 bytes:
    +--------+--------+--------+--------+========+
    |  0xc8  |YYYYYYYY|YYYYYYYY|  type  |  data  |
    +--------+--------+--------+--------+========+

    ext 32 stores an integer and a byte array whose length is upto (2^32)-1 bytes:
    +--------+--------+--------+--------+--------+--------+========+
    |  0xc9  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|  type  |  data  |
    +--------+--------+--------+--------+--------+--------+========+

    where
    * XXXXXXXX is a 8-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a big-endian 32-bit unsigned integer which represents N
    * N is a length of data
    * type is a signed 8-bit signed integer
    * type < 0 is reserved for future extension including 2-byte type information

### Timestamp extension type

Timestamp extension type is assigned to extension type `-1`. It defines 3 formats: 32-bit format, 64-bit format, and 96-bit format.

    timestamp 32 stores the number of seconds that have elapsed since 1970-01-01 00:00:00 UTC
    in an 32-bit unsigned integer:
    +--------+--------+--------+--------+--------+--------+
    |  0xd6  |   -1   |   seconds in 32-bit unsigned int  |
    +--------+--------+--------+--------+--------+--------+

    timestamp 64 stores the number of seconds and nanoseconds that have elapsed since 1970-01-01 00:00:00 UTC
    in 32-bit unsigned integers:
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd7  |   -1   |nanoseconds in 30-bit unsigned int |  seconds in 34-bit unsigned int   |
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+

    timestamp 96 stores the number of seconds and nanoseconds that have elapsed since 1970-01-01 00:00:00 UTC
    in 64-bit signed integer and 32-bit unsigned integer:
    +--------+--------+--------+--------+--------+--------+--------+
    |  0xc7  |   12   |   -1   |nanoseconds in 32-bit unsigned int |
    +--------+--------+--------+--------+--------+--------+--------+
    +--------+--------+--------+--------+--------+--------+--------+--------+
                        seconds in 64-bit signed int                        |
    +--------+--------+--------+--------+--------+--------+--------+--------+

* Timestamp 32 format can represent a timestamp in [1970-01-01 00:00:00 UTC, 2106-02-07 06:28:16 UTC) range. Nanoseconds part is 0.
* Timestamp 64 format can represent a timestamp in [1970-01-01 00:00:00.000000000 UTC, 2514-05-30 01:53:04.000000000 UTC) range.
* Timestamp 96 format can represent a timestamp in [-584554047284-02-23 16:59:44 UTC, 584554051223-11-09 07:00:16.000000000 UTC) range.
* In timestamp 64 and timestamp 96 formats, nanoseconds must not be larger than 999999999.

Pseudo code for serialization:

    struct timespec {
        long tv_sec;  // seconds
        long tv_nsec; // nanoseconds
    } time;
    if ((time.tv_sec >> 34) == 0) {
        uint64_t data64 = (time.tv_nsec << 34) | time.tv_sec;
        if (data64 & 0xffffffff00000000L == 0) {
            // timestamp 32
            uint32_t data32 = data64;
            serialize(0xd6, -1, data32)
        }
        else {
            // timestamp 64
            serialize(0xd7, -1, data64)
        }
    }
    else {
        // timestamp 96
        serialize(0xc7, 12, -1, time.tv_nsec, time.tv_sec)
    }

Pseudo code for deserialization:

     ExtensionValue value = deserialize_ext_type();
     struct timespec result;
     switch(value.length) {
     case 4:
         uint32_t data32 = value.payload;
         result.tv_nsec = 0;
         result.tv_sec = data32;
     case 8:
         uint64_t data64 = value.payload;
         result.tv_nsec = data64 >> 34;
         result.tv_sec = data64 & 0x00000003ffffffffL;
     case 12:
         uint32_t data32 = value.payload;
         uint64_t data64 = value.payload + 4;
         result.tv_nsec = data32;
         result.tv_sec = data64;
     default:
         // error
     }

### bigint extension type

The bigint extension is assigned to the type -2 and allows to store large integers. Support for big integers
is optional, but recommended for implementations whose language or standard library provide integer types
larger than 64 bit (including variable size integers). This extension uses the following formats as defined above
for fixext 16, ext 8, ext 16 and ext 32:

    int 128 stores the type -2 and a 128 bit (16 byte) big endian signed integer
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd8  |  -2    |                                 bigint                                  
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    +--------+--------+--------+--------+--------+--------+--------+--------+
                                 bigint (cont.)                             |
    +--------+--------+--------+--------+--------+--------+--------+--------+

    bigint 8 stores an 8 bit signed integer with the payload size, the type -2 and a bigint payload whose length is upto (2^8)-1 bytes:
    +--------+--------+--------+========+
    |  0xc7  |XXXXXXXX|   -2   | bigint |
    +--------+--------+--------+========+

    bigint 16 stores an 16 bit signed integer with the payload size, the type -2 and a bigint payload whose length is upto (2^16)-1 bytes:
    +--------+--------+--------+--------+========+
    |  0xc8  |YYYYYYYY|YYYYYYYY|   -2   | bigint |
    +--------+--------+--------+--------+========+

    bigint 32 stores an 16 bit signed integer with the payload size, the type -2 and a bigint payload whose length is upto (2^32)-1 bytes:
    +--------+--------+--------+--------+--------+--------+========+
    |  0xc9  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|   -2   | bigint |
    +--------+--------+--------+--------+--------+--------+========+

    where
    * XXXXXXXX is a 8-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a big-endian 32-bit unsigned integer which represents N
    * N is the length of the bigint payload size
    * bigint is the bytes of an unsigned integer in big endian representation

    Recommendations:
    * Integer values which fit into 64 or less bits should be encoded using an appropriate non-extension integer type, as defined above in "int format family", to enhance backwards compatibility
    * Leading 0x00 bytes for positive numbers should be omitted, producing the shortest possible representation of a given value
    * Leading 0xff bytes of the values for negative numbers should be omitted if possible. (A single 0xff byte may be necessary if the most significant bit of the next byte is 0, to distinguish the negative number from positive numbers.)
    
### bigfloat extension type

The bigfloat extension is assigned to the type -3 and allows to store large / high precision binary floating point values.
Support for bigfloats is optional, but recommended for implementations whose language or standard library provide
float types with higher range or precision than IEEE 64 bit. This extension the following formats as defined above for
fixext 16, ext 8, ext 16 and ext 32, with the payload defined by the IEEE 754-2008 interchange format.

    float 128 stores the type -3 and a 128 bit (16 byte) "quad" floating point number as defined in IEEE 754-2008
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd8  |  -3    |                               bigfloat 128                                  
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    +--------+--------+--------+--------+--------+--------+--------+--------+
                               bigfloat 128 (cont.)                         |
    +--------+--------+--------+--------+--------+--------+--------+--------+

    bigfloat 8 stores an 8 bit signed integer with the payload size, the type -2 and a payload in the IEEE 754-2008 interchange format whose length is upto (2^8)-1 bytes:
    +--------+--------+--------+========+
    |  0xc7  |XXXXXXXX|   -3   |bigfloat|
    +--------+--------+--------+========+

    bigfloat 16 stores an 16 bit signed integer with the payload size, the type -2 and a payload in the IEEE 754-2008 interchange format whose length is upto (2^16)-1 bytes:
    +--------+--------+--------+--------+========+
    |  0xc8  |YYYYYYYY|YYYYYYYY|   -3   |bigfloat|
    +--------+--------+--------+--------+========+

    bigfloat 32 stores an 16 bit signed integer with the payload size, the type -2 and a payload in the IEEE 754-2008 interchange format whose length is upto (2^32)-1 bytes:
    +--------+--------+--------+--------+--------+--------+========+
    |  0xc9  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|   -3   |bigfloat|
    +--------+--------+--------+--------+--------+--------+========+

    where
    * XXXXXXXX is a 8-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a big-endian 32-bit unsigned integer which represents N
    * N is the length of the bigfloat payload size
    * As required by the IEEE 754-2008 interchange format definition, N must be a multiple of 4 bytes (32 bit).
    * N must be at least 20 (use "float 128" for 16 byte / 128 bit values)
    
    Recommendations for encoders and applications:
    * Encoders should use the shortest possible exact representation of a given value, including float32 and float64 where appropriate. E. g. the value 10.5 will fit into an float32.
    * Similarly, the values for "Infinity" and "Negative Infinity" can be encoded as float32.
    * As the semantics of the payload bits of NaNs are implementation defined, applications should not rely on different NaN values, and just treat them as a single value.
    * As signaling NaNs may lead to exceptions on some hardware just when reading the value, and be quietly converted to non-signaling NaNs on other hardware, applications should avoid signaling NaNs.
    
### Bigdecimal extension types

The bigdecimal extension types are assigned to the type -4 and -5 and allow to store large / high precision decimal floating point values.
Support for bigdecimals is optional, but recommended for implementations whose language or standard library provide
decimal data types. This extension the following formats as defined above for fixext 4, fixext 8, fixext 16, ext 8, ext 16 and ext 32, 
with the payload defined by the IEEE 754-2008 interchange format. Type -4 refers to numbers encoded using the decimal encoding, while
while Type -5 refers to the binary encoding, as defined in the IEEE 754-2008 standard.


    decimal 32 stores the type (-4 / -5) and a 32 bit decimal floating point number as defined in IEEE 754-2008
    +--------+--------+--------+--------+--------+--------+
    |  0xd6  | -4/-5  |             decimal 32            |
    +--------+--------+--------+--------+--------+--------+

    decimal 64 stores the type (-4 / -5) and a 64 bit "basic format" decimal number.
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd7  | -4/-5  |                               decimal 64                              |
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+

    decimal 128 stores the type (-4 / -5) and a 128 bit "basic format" decimal floating point number as defined in IEEE 754-2008
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd8  | -4/-5  |                               decimal 128                                  
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    +--------+--------+--------+--------+--------+--------+--------+--------+
                                decimal 128 (cont.)                         |
    +--------+--------+--------+--------+--------+--------+--------+--------+

    bigdecimal 8 stores an 8 bit signed integer with the payload size, the type (-4 / -5) and a payload in the IEEE 754-2008 interchange format whose length is upto (2^8)-1 bytes:
    +--------+--------+--------+========+
    |  0xc7  |XXXXXXXX| -4/-5  |bigfloat|
    +--------+--------+--------+========+

    bigdecimal 16 stores an 16 bit signed integer with the payload size, the type (-4 / -5) and a payload in the IEEE 754-2008 interchange format whose length is upto (2^16)-1 bytes:
    +--------+--------+--------+--------+========+
    |  0xc8  |YYYYYYYY|YYYYYYYY| -4/-5  |bigfloat|
    +--------+--------+--------+--------+========+

    bigdecimal 32 stores an 16 bit signed integer with the payload size, the type (-4 / -5) and a payload in the IEEE 754-2008 interchange format whose length is upto (2^32)-1 bytes:
    +--------+--------+--------+--------+--------+--------+========+
    |  0xc9  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ| -4/-5  |bigfloat|
    +--------+--------+--------+--------+--------+--------+========+

    where
    * XXXXXXXX is a 8-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a big-endian 32-bit unsigned integer which represents N
    * N is the length of the bigfloat payload size (expsize + bigfloat)
    * As required by the IEEE 754-2008 interchange format definition, N must be a multiple of 4 bytes (32 bit).
    * When possible, use the "fixext" formats: for N=32, use "decimal 4", for N=64, use "decimal 8" and for N=128, use "decimal 128" format.
    
    Recommendations for encoders and applications:
    * A given application / profile should specify whether decimal or binar representation is to be used.
    * Encoders should produce canonical encodings as defined in section 3.5.2 of IEEE 754-2008. 
    
    
### fractions extension type

The fractions extension is assigned to the type -6 and allows to store fractional values and decimal floating point values.
Support for fractions is optional, but recommended for implementations whose language or standard library provide
fractions data types. All payloads consist of 1 or 2 objects from the int or bigint families.

    fraction 1 stores the type -6 and a payload whose length is 1 byte
    +--------+--------+--------+
    |  0xd4  |   -6   |fraction|
    +--------+--------+--------+

    fraction 2 stores the type -6 and a payload whose length is 2 bytes
    +--------+--------+--------+--------+
    |  0xd5  |   -6   |     fraction    |
    +--------+--------+--------+--------+

    fraction 4 stores the type -6 and a payload whose length is 4 bytes
    +--------+--------+--------+--------+--------+--------+
    |  0xd6  |   -6   |              fraction             |
    +--------+--------+--------+--------+--------+--------+

    fraction 8 stores the type -6 and a payload whose length is 8 bytes
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd7  |   -6   |                               fraction                                |
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+

    fraction 16 stores the type -6 and a payload whose length is 16 bytes
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    |  0xd8  |   -6   |                                fraction                                  
    +--------+--------+--------+--------+--------+--------+--------+--------+--------+--------+
    +--------+--------+--------+--------+--------+--------+--------+--------+
                                fraction (cont.)                            |
    +--------+--------+--------+--------+--------+--------+--------+--------+

    bigfraction 8 stores an 8 bit signed integer with the payload size, the type -6 and a payload whose length is upto (2^8)-1 bytes:
    +--------+--------+--------+========+
    |  0xc7  |XXXXXXXX|   -6   |fraction|
    +--------+--------+--------+========+

    bigfraction 16 stores an 16 bit signed integer with the payload size, the type -6 and a payload whose length is upto (2^16)-1 bytes:
    +--------+--------+--------+--------+========+
    |  0xc8  |YYYYYYYY|YYYYYYYY|   -6   |fraction|
    +--------+--------+--------+--------+========+

    bigfraction 32 stores an 16 bit signed integer with the payload size, the type -6 and a payload whose length is upto (2^32)-1 bytes:
    +--------+--------+--------+--------+--------+--------+========+
    |  0xc9  |ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|ZZZZZZZZ|   -6   |fraction|
    +--------+--------+--------+--------+--------+--------+========+

    where
    * XXXXXXXX is a 8-bit unsigned integer which represents N
    * YYYYYYYY_YYYYYYYY is a 16-bit big-endian unsigned integer which represents N
    * ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ_ZZZZZZZZ is a big-endian 32-bit unsigned integer which represents N
    * N is the length of the fraction payload size
    * fraction is the concatenation of 1 to 2 integers, each of them encoded as defined in the "int format family" or "bigint extension type" sections above:
    ** If there is only one number, it is considered the denominator, and the numerator is 1.
    ** In all other cases, the numerator is the first given number, and the denominator is the second given number.
    * Any possible payload after the fourth number is reserved for future extensions of the specification, and must not be produced by current encoders. Readers should signal an error when they encounter unknown content after the 4 numbers.
    
    Recommendations for encoders and applications:
    * Encoders should prefer short representations, if possible.
    * If the denominator is 1, the number should be encoded using the integer types, not as fraction.
    * For denominator, prefer unsigned integer types (except if the base exceeds 64 bit).
    * To encode NaN, Infinity and negative infinity, use the appropriate float 32 values.
    * If the application does not have different requirements, encoders should reduce the fractions before writing them.


## Serialization: type to format conversion

MessagePack serializers convert MessagePack types into formats as following:

<table>
  <tr><th>source types</th><th>output format</th></tr>
  <tr><td>Integer</td><td>int format family (positive fixint, negative fixint, int 8/16/32/64 or uint 8/16/32/64)</td></tr>
  <tr><td>Nil</td><td>nil</td></tr>
  <tr><td>Boolean</td><td>bool format family (false or true)</td></tr>
  <tr><td>Float</td><td>float format family (float 32/64)</td></tr>
  <tr><td>String</td><td>str format family (fixstr or str 8/16/32)</td></tr>
  <tr><td>Binary</td><td>bin format family (bin 8/16/32)</td></tr>
  <tr><td>Array</td><td>array format family (fixarray or array 16/32)</td></tr>
  <tr><td>Map</td><td>map format family (fixmap or map 16/32)</td></tr>
  <tr><td>Extension</td><td>ext format family (fixext or ext 8/16/32)</td></tr>
</table>

If an object can be represented in multiple possible output formats, serializers SHOULD use the format which represents the data in the smallest number of bytes.

## Deserialization: format to type conversion

MessagePack deserializers convert MessagePack formats into types as following:

<table>
  <tr><th>source formats</th><th>output type</th></tr>
  <tr><td>positive fixint, negative fixint, int 8/16/32/64 and uint 8/16/32/64</td><td>Integer</td></tr>
  <tr><td>nil</td><td>Nil</td></tr>
  <tr><td>false and true</td><td>Boolean</td></tr>
  <tr><td>float 32/64</td><td>Float</td></tr>
  <tr><td>fixstr and str 8/16/32</td><td>String</td></tr>
  <tr><td>bin 8/16/32</td><td>Binary</td></tr>
  <tr><td>fixarray and array 16/32</td><td>Array</td></tr>
  <tr><td>fixmap map 16/32</td><td>Map</td></tr>
  <tr><td>fixext and ext 8/16/32</td><td>Extension</td></tr>
</table>

## Future discussion

### Profile

Profile is an idea that Applications restrict the semantics of MessagePack while sharing the same syntax to adapt MessagePack for certain use cases.

For example, applications may remove Binary type, restrict keys of map objects to be String type, and put some restrictions to make the semantics compatible with JSON. Applications which use schema may remove String and Binary types and deal with byte arrays as Raw type. Applications which use hash (digest) of serialized data may sort keys of maps to make the serialized data deterministic.
Profiles may also restrict floating point to one of 32 or 64 bit, and define which (sub-)set of extension types need to be supported.

## Implementation guidelines

### Upgrading MessagePack specification

MessagePack specification is changed at this time.
Here is a guideline to upgrade existent MessagePack implementations:

* In a minor release, deserializers support the bin format family and str 8 format. The type of deserialized objects should be same with raw 16 (== str 16) or raw 32 (== str 32)
* In a major release, serializers distinguish Binary type and String type using bin format family and str format family
  * At the same time, serializers should offer "compatibility mode" which doesn't use bin format family and str 8 format


___

    MessagePack specification
    Last modified at 2017-08-09 22:42:07 -0700
    Sadayuki Furuhashi © 2013-04-21 21:52:33 -0700
