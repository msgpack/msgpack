--TEST--
Check for reference serialization
--SKIPIF--
<?php
if (version_compare(PHP_VERSION, '5.3.2') <= 0) {
    echo "skip tests in PHP 5.3.3 or newer";
}
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

$a = array('foo');

test('array($a, $a)', array($a, $a), false);
test('array(&$a, &$a)', array(&$a, &$a), false);

$a = array(null);
$b = array(&$a);
$a[0] = &$b;

test('cyclic', $a, true);

var_dump($a);
var_dump(msgpack_unserialize(msgpack_serialize($a)));

--EXPECT--
array($a, $a)
82008100a3666f6f018100a3666f6f
array(2) {
  [0]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
  [1]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
}
OK
array(&$a, &$a)
820082c00100a3666f6f0182c0020002
array(2) {
  [0]=>
  &array(1) {
    [0]=>
    string(3) "foo"
  }
  [1]=>
  &array(1) {
    [0]=>
    string(3) "foo"
  }
}
OK
cyclic
810082c0010082c0010082c0020002
array(1) {
  [0]=>
  &array(1) {
    [0]=>
    &array(1) {
      [0]=>
      *RECURSION*
    }
  }
}
OK
array(1) {
  [0]=>
  &array(1) {
    [0]=>
    &array(1) {
      [0]=>
      *RECURSION*
    }
  }
}
array(1) {
  [0]=>
  &array(1) {
    [0]=>
    &array(1) {
      [0]=>
      *RECURSION*
    }
  }
}
