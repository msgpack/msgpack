--TEST--
Extra bytes buffered streaming unserialization
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable, $test = null) {
    $unpacker = new MessagePackUnpacker();

    foreach ($variable as $var)
    {
        $serialized = pack('H*', $var);

        $length = strlen($serialized);

        for ($i = 0; $i < $length;) {
            $len = rand(1, 10);
            $str = substr($serialized, $i, $len);

            $unpacker->feed($str);

            while (true) {
                if ($unpacker->execute()) {
                    $unserialized = $unpacker->data();
                    var_dump($unserialized);
                    $unpacker->reset();
                } else {
                    break;
                }
            }
            $i += $len;
        }
    }
}

test('array(1, 2, 3)', array('9301020392'));
test('array(1, 2, 3), array(3, 9), 4', array('9301020392', '030904'));
--EXPECTF--
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
array(2) {
  [0]=>
  int(3)
  [1]=>
  int(9)
}
int(4)
