--TEST--
Check for bool serialisation
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

test('bool true',  true);
test('bool false', false);
?>
--EXPECT--
bool true
c3
bool(true)
OK
bool false
c2
bool(false)
OK
