--TEST--
Object test
--SKIPIF--
<?php
if (version_compare(PHP_VERSION, '5.2.0') < 0) {
    echo "skip tests in PHP 5.2 or newer";
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

class Obj {
    public $a;
    protected $b;
    private $c;

    function __construct($a, $b, $c) {
        $this->a = $a;
        $this->b = $b;
        $this->c = $c;
    }
}

$o = new Obj(1, 2, 3);


test('object', $o, false);
?>
--EXPECTF--
object
84c0a34f626aa16101a4002a006202a6004f626a006303
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
  int(3)
}
OK
