--TEST--
Object test, incomplete class
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable, $test) {
    $serialized = pack('H*', $variable);
    $unserialized = msgpack_unserialize($serialized);

    echo $type, PHP_EOL;
    echo bin2hex($serialized), PHP_EOL;
    var_dump($unserialized);
}

test('incom', '83c0a34f626aa16101a16202', false);
?>
--EXPECTF--
incom
83c0a34f626aa16101a16202
object(__PHP_Incomplete_Class)#%d (3) {
  ["__PHP_Incomplete_Class_Name"]=>
  string(3) "Obj"
  ["a"]=>
  int(1)
  ["b"]=>
  int(2)
}
