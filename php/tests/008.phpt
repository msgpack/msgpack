--TEST--
Check for array+string serialization
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
    echo bin2hex($serialized),  PHP_EOL;
    var_dump($unserialized);
    echo $unserialized == $variable ? 'OK' : 'ERROR', PHP_EOL;
}

test('array("foo", "foo", "foo")', array("foo", "foo", "foo"));
test('array("one" => 1, "two" => 2))', array("one" => 1, "two" => 2));
test('array("kek" => "lol", "lol" => "kek")', array("kek" => "lol", "lol" => "kek"));
test('array("" => "empty")', array("" => "empty"));
?>
--EXPECT--
array("foo", "foo", "foo")
93a3666f6fa3666f6fa3666f6f
array(3) {
  [0]=>
  string(3) "foo"
  [1]=>
  string(3) "foo"
  [2]=>
  string(3) "foo"
}
OK
array("one" => 1, "two" => 2))
82a36f6e6501a374776f02
array(2) {
  ["one"]=>
  int(1)
  ["two"]=>
  int(2)
}
OK
array("kek" => "lol", "lol" => "kek")
82a36b656ba36c6f6ca36c6f6ca36b656b
array(2) {
  ["kek"]=>
  string(3) "lol"
  ["lol"]=>
  string(3) "kek"
}
OK
array("" => "empty")
81a0a5656d707479
array(1) {
  [""]=>
  string(5) "empty"
}
OK
