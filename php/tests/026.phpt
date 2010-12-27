--TEST--
Cyclic array test
--INI--
--SKIPIF--
<?php
if ((version_compare(PHP_VERSION, '5.2.13') <= 0) ||
    (version_compare(PHP_VERSION, '5.3.0') >= 0 &&
     version_compare(PHP_VERSION, '5.3.2') <= 0)) {
    echo "skip tests in PHP 5.2.14/5.3.3 or newer";
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

$a = array(
    'a' => array(
        'b' => 'c',
        'd' => 'e'
    ),
);

$a['f'] = &$a;

test('array', $a, true);

$a = array("foo" => &$b);
$b = array(1, 2, $a);
var_dump($a);
var_dump($k = msgpack_unserialize(msgpack_serialize($a)));

$k["foo"][1] = "b";
var_dump($k);
?>
--EXPECT--
array
82a16182a162a163a164a165a16683c001a16182a162a163a164a165a16682c0020003
array(2) {
  ["a"]=>
  array(2) {
    ["b"]=>
    string(1) "c"
    ["d"]=>
    string(1) "e"
  }
  ["f"]=>
  &array(2) {
    ["a"]=>
    array(2) {
      ["b"]=>
      string(1) "c"
      ["d"]=>
      string(1) "e"
    }
    ["f"]=>
    *RECURSION*
  }
}
OK
array(1) {
  ["foo"]=>
  &array(3) {
    [0]=>
    int(1)
    [1]=>
    int(2)
    [2]=>
    *RECURSION*
  }
}
array(1) {
  ["foo"]=>
  &array(3) {
    [0]=>
    int(1)
    [1]=>
    int(2)
    [2]=>
    array(1) {
      ["foo"]=>
      *RECURSION*
    }
  }
}
array(1) {
  ["foo"]=>
  &array(3) {
    [0]=>
    int(1)
    [1]=>
    string(1) "b"
    [2]=>
    array(1) {
      ["foo"]=>
      *RECURSION*
    }
  }
}
