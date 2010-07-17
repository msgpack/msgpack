--TEST--
Check for array unserialization
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable) {
    $unserialized = msgpack_unserialize(pack('H*', $variable));

    echo $type, PHP_EOL;
    echo $variable, PHP_EOL;
    var_dump($unserialized);
}

test('empty array:', '90');
test('array(1, 2, 3)', '93010203');
test('array(array(1, 2, 3), arr...', '93930102039304050693070809');
test('array("foo", "FOO", "Foo")', '93a3666f6fa3464f4fa3466f6f');
test('array(1, 123.45,  true, ...', '9701cb405edccccccccccdc3c293010293090807c0a3666f6f');
?>
--EXPECT--
empty array:
90
array(0) {
}
array(1, 2, 3)
93010203
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
array(array(1, 2, 3), arr...
93930102039304050693070809
array(3) {
  [0]=>
  array(3) {
    [0]=>
    int(1)
    [1]=>
    int(2)
    [2]=>
    int(3)
  }
  [1]=>
  array(3) {
    [0]=>
    int(4)
    [1]=>
    int(5)
    [2]=>
    int(6)
  }
  [2]=>
  array(3) {
    [0]=>
    int(7)
    [1]=>
    int(8)
    [2]=>
    int(9)
  }
}
array("foo", "FOO", "Foo")
93a3666f6fa3464f4fa3466f6f
array(3) {
  [0]=>
  string(3) "foo"
  [1]=>
  string(3) "FOO"
  [2]=>
  string(3) "Foo"
}
array(1, 123.45,  true, ...
9701cb405edccccccccccdc3c293010293090807c0a3666f6f
array(7) {
  [0]=>
  int(1)
  [1]=>
  float(123.45)
  [2]=>
  bool(true)
  [3]=>
  bool(false)
  [4]=>
  array(3) {
    [0]=>
    int(1)
    [1]=>
    int(2)
    [2]=>
    array(3) {
      [0]=>
      int(9)
      [1]=>
      int(8)
      [2]=>
      int(7)
    }
  }
  [5]=>
  NULL
  [6]=>
  string(3) "foo"
}
