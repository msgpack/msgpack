--TEST--
Check for integer serialisation
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

test('zero: 0', 0);
test('small: 1',  1);
test('small: -1',  -1);
test('medium: 1000', 1000);
test('medium: -1000', -1000);
test('large: 100000', 100000);
test('large: -100000', -100000);
?>
--EXPECT--
zero: 0
00
int(0)
OK
small: 1
01
int(1)
OK
small: -1
ff
int(-1)
OK
medium: 1000
cd03e8
int(1000)
OK
medium: -1000
d1fc18
int(-1000)
OK
large: 100000
ce000186a0
int(100000)
OK
large: -100000
d2fffe7960
int(-100000)
OK
