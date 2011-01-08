--TEST--
Object test, array of objects with __sleep
--SKIPIF--
<?php
if (version_compare(PHP_VERSION, '5.2.0') >= 0) {
    echo "skip tests in PHP 5.1 or older";
}
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable, $test) {
    $serialized = msgpack_serialize($variable);
    $unserialized = msgpack_unserialize($serialized);

    var_dump($variable);
    var_dump($unserialized);
}

class Obj {
    public $a;
    protected $b;
    private $c;
    var $d;

    function __construct($a, $b, $c, $d) {
        $this->a = $a;
        $this->b = $b;
        $this->c = $c;
        $this->d = $d;
    }

    function __sleep() {
        return array('a', 'b', 'c');
    }

#   function __wakeup() {
#       $this->d = $this->a + $this->b + $this->c;
#   }
}

$array = array(
    new Obj("aa", "bb", "cc", "dd"),
    new Obj("ee", "ff", "gg", "hh"),
    new Obj(1, 2, 3, 4),
);


test('array', $array, true);
?>
--EXPECTF--
array(3) {
  [0]=>
  object(Obj)#1 (4) {
    ["a"]=>
    string(2) "aa"
    ["b:protected"]=>
    string(2) "bb"
    ["c:private"]=>
    string(2) "cc"
    ["d"]=>
    string(2) "dd"
  }
  [1]=>
  object(Obj)#2 (4) {
    ["a"]=>
    string(2) "ee"
    ["b:protected"]=>
    string(2) "ff"
    ["c:private"]=>
    string(2) "gg"
    ["d"]=>
    string(2) "hh"
  }
  [2]=>
  object(Obj)#3 (4) {
    ["a"]=>
    int(1)
    ["b:protected"]=>
    int(2)
    ["c:private"]=>
    int(3)
    ["d"]=>
    int(4)
  }
}
array(3) {
  [0]=>
  object(Obj)#4 (4) {
    ["a"]=>
    string(2) "aa"
    ["b:protected"]=>
    string(2) "bb"
    ["c:private"]=>
    string(2) "cc"
    ["d"]=>
    NULL
  }
  [1]=>
  object(Obj)#5 (4) {
    ["a"]=>
    string(2) "ee"
    ["b:protected"]=>
    string(2) "ff"
    ["c:private"]=>
    string(2) "gg"
    ["d"]=>
    NULL
  }
  [2]=>
  object(Obj)#6 (4) {
    ["a"]=>
    int(1)
    ["b:protected"]=>
    int(2)
    ["c:private"]=>
    int(3)
    ["d"]=>
    NULL
  }
}
