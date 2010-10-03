--TEST--
Check for simple string serialization
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable) {
    $serialized = msgpack_serialize($variable);
    $unserialized = msgpack_unserialize($serialized);

    echo $type, PHP_EOL;
    echo bin2hex($serialized), PHP_EOL;
    var_dump($unserialized);
    echo $unserialized === $variable ? 'OK' : 'ERROR', PHP_EOL;
}

test('empty: ""', "");
test('string: "foobar"', "foobar");
?>
--EXPECT--
empty: ""
a0
string(0) ""
OK
string: "foobar"
a6666f6f626172
string(6) "foobar"
OK
