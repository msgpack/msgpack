--TEST--
Extra bytes unbuffered streaming unserialization
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable, $test = null) {
    $unpacker = new MessagePackUnpacker();

    $str = "";
    $offset = 0;

    foreach ($variable as $var)
    {
        $serialized = pack('H*', $var);

        $length = strlen($serialized);

        for ($i = 0; $i < $length;) {
            $len = rand(1, 10);
            $str .= substr($serialized, $i, $len);

            while (true) {
                if ($unpacker->execute($str, $offset)) {
                    $unserialized = $unpacker->data();
                    var_dump($unserialized);

                    $unpacker->reset();
                    $str = substr($str, $offset);
                    $offset = 0;
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
