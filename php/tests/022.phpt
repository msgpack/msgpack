--TEST--
Object test, unserialize_callback_func
--SKIPIF--
--INI--
unserialize_callback_func=autoload
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
    echo $test || $unserialized->b == 2 ? 'OK' : 'ERROR', PHP_EOL;
}

function autoload($classname) {
    class Obj {
        var $a;
        var $b;

        function __construct($a, $b) {
            $this->a = $a;
            $this->b = $b;
        }
    }
}

test('autoload', '83c0a34f626aa16101a16202', false);
?>
--EXPECTF--
autoload
83c0a34f626aa16101a16202
object(Obj)#%d (2) {
  ["a"]=>
  int(1)
  ["b"]=>
  int(2)
}
OK
