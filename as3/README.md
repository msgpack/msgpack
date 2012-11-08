# as3-msgpack v0.4.1
<p>as3-msgpack is a implementation of MessagePack specification for Actionscript3 language (Flash, Flex and AIR).</p>
<p>The decoder/encoder functions were based on Java implementation: https://github.com/msgpack/msgpack-java</p>
<p>See online documentation: http://disturbedcoder.com/files/as3-msgpack/</p>

## about message pack format
<p>MessagePack is an efficient binary serialization format. It lets you exchange data among multiple languages like JSON but it's faster and smaller. For example, small integers (like flags or error code) are encoded into a single byte, and typical short strings only require an extra byte in addition to the strings themselves.</p>
<p>Check the website: http://msgpack.org</p>

## examples
### basic encoding/decoding
```actionscript
var bytes:ByteArray = MessagePack.encoder.write(42); // encode a number
bytes.position = 0;
trace(MessagePack.decoder.read(bytes)); // voilá!
```

### encoding arrays
```actionscript
var bytes:ByteArray = MessagePack.encoder.write([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]); // encode an array
bytes.position = 0;
trace(MessagePack.decoder.read(bytes)); // voilá!
```

### encoding objects
```actionscript
var bytes:ByteArray = MessagePack.encoder.write({myNumber: 42, myName: "Lucas"}); // encode an object
bytes.position = 0;
var obj:Object = MessagePack.decoder.read(bytes);

for (var key:String in obj)
	trace(key + " = " + obj[key]); // print each element of the object
```
<p>Note that Strings are stored as raw bytes (UTF format). If you need to manipulate it after decoding you'll need to read the data into the ByteArray as a String (or calling toString method).</p>

### encoder/decoder interfaces
<p>Differently from the previous version, write and read functions doesn't work with ByteArray class directly. To read/write data you must use any class which implements IDataInput/IDataOutput interfaces. Thus, it's possible to use this library with ByteArray, FileStream, Socket and URLStream classes.</p>
```actionscript
var operation:Array = [operationID, param1, param2];
// say we'll write the encoded object directly into an existing Socket instance
MessagePack.encoder.write(operation, socket);
```

## generating binaries and documentation
<p>You may use this library just copying the source files to your project, so when compiling it, as3-msgpack classes will be already included. However, you may prefer to use pre-compiled binaries (which can improve the compiling time of your project). You can download the binaries straight from the repository, or download the latest tag.</p>
<p>In the case you want to recompile the project by your self, you'll need to install FlexSDK (as3-msgpack compiles for Flash Player 9 or above). See the following instructions for more details.</p>
<p>Note: FlexSDK binaries must be in your PATH to run the following commands.</p>

### compiling test application
<p>At the root folder of the project (as3-msgpack), type the following command:</p>
```
mxmlc -default-frame-rate=30 -default-size=800,600 -static-link-runtime-shared-libraries=true -source-path+=src/ -library-path+=lib/ -output=bin/MessagePackTest.swf -- src/org/msgpack/MessagePackTest.as
```
<p>The file MessagePackTest.swf will be generated in bin folder.</p>

### compiling library
<p>At the root folder of the project (as3-msgpack), type the following command:</p>
```
compc -include-sources+=src/org/msgpack/MessagePackBase.as -include-sources+=src/org/msgpack/MessagePackDecoder.as -include-sources+=src/org/msgpack/MessagePackEncoder.as -include-sources+=src/org/msgpack/TypeHandler.as -include-sources+=src/org/msgpack/TypeMap.as -output=bin/MessagePack.swc
```
<p>The file MessagePack.swc will be generated in bin folder.</p>

### generating documentation
<p>At the root folder of the project (as3-msgpack), type the following command:</p>
```
asdoc -main-title=as3-msgpack0.4.1 -warnings=false -output=doc/ -doc-sources+=src/ -library-path+=lib/as3console.swc
```
<p>The file documentation will be generated in doc folder.</p>