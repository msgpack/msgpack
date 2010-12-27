--TEST--
Object Serializable interface
--SKIPIF--
<?php
if (version_compare(PHP_VERSION, '5.1.0') < 0) {
    echo "skip tests in PHP 5.1 or newer";
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

class Obj implements Serializable {
    var $a;
    var $b;

    function __construct($a, $b) {
        $this->a = $a;
        $this->b = $b;
    }

    public function serialize() {
        return pack('NN', $this->a, $this->b);
    }

    public function unserialize($serialized) {
        $tmp = unpack('N*', $serialized);
        $this->__construct($tmp[1], $tmp[2]);
    }
}

$o = new Obj(1, 2);

test('object', $o, false);
?>
--EXPECTF--
object
82c003a34f626aa80000000100000002
object(Obj)#%d (2) {
  ["a"]=>
  int(1)
  ["b"]=>
  int(2)
}
OK
