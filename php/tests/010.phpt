--TEST--
Array test
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable, $test) {
    $serialized = msgpack_serialize($variable);
    $unserialized = msgpack_unserialize($serialized);

    echo $type, PHP_EOL;
    echo bin2hex($serialized), PHP_EOL;
    var_dump($unserialized);
    echo $test || $unserialized == $variable ? 'OK' : 'ERROR', PHP_EOL;
}

$a = array(
    'a' => array(
        'b' => 'c',
        'd' => 'e'
    ),
    'f' => array(
        'g' => 'h'
    )
);

test('array', $a, false);
?>
--EXPECT--
array
82a16182a162a163a164a165a16681a167a168
array(2) {
  ["a"]=>
  array(2) {
    ["b"]=>
    string(1) "c"
    ["d"]=>
    string(1) "e"
  }
  ["f"]=>
  array(1) {
    ["g"]=>
    string(1) "h"
  }
}
OK
