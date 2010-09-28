--TEST--
Unserialize invalid data
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

$datas = array(
    87817,
    -1,
    array(1,2,3,"testing" => 10, "foo"),
    true,
    false,
    0.187182,
    "dakjdh98389\000",
    null,
    (object)array(1,2,3),
);

error_reporting(0);

foreach ($datas as $data) {
    $str = msgpack_serialize($data);
    $len = strlen($str);

    // truncated
    for ($i = 0; $i < $len - 1; $i++) {
        $v = msgpack_unserialize(substr($str, 0, $i));

        if (is_object($data) || is_array($data)) {
            if ($v !== null && $v !== false && $v != $data) {
                echo "output at $i:\n";
                var_dump($v);
            }
        } else if ($v !== null && $v == $data) {
            continue;
        } else if ($v !== null && $v !== $data) {
            echo "output at $i:\n";
            var_dump($v);
            echo "vs.\n";
            var_dump($data);
        }
    }

    // padded
    $str .= "98398afa\000y21_ ";
    $v = msgpack_unserialize($str);
    if ($v !== $data && !(is_object($data) && $v == $data)) {
        echo "padded should get original\n";
        var_dump($v);
        echo "vs.\n";
        var_dump($data);
    }
}
?>
--EXPECTF--
output at 3:
array(1) {
  [0]=>
  int(1)
}
output at 4:
array(1) {
  [0]=>
  int(1)
}
output at 5:
array(2) {
  [0]=>
  int(1)
  [1]=>
  int(2)
}
output at 6:
array(2) {
  [0]=>
  int(1)
  [1]=>
  int(2)
}
output at 7:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 8:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 9:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 10:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 11:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 12:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 13:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 14:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 15:
array(3) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
}
output at 16:
array(4) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
  ["testing"]=>
  int(10)
}
output at 17:
array(4) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
  ["testing"]=>
  int(10)
}
output at 18:
array(4) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
  ["testing"]=>
  int(10)
}
output at 19:
array(4) {
  [0]=>
  int(1)
  [1]=>
  int(2)
  [2]=>
  int(3)
  ["testing"]=>
  int(10)
}
output at 11:
object(stdClass)#2 (0) {
}
output at 12:
object(stdClass)#3 (0) {
}
output at 13:
object(stdClass)#2 (1) {
  [0]=>
  int(1)
}
output at 14:
object(stdClass)#3 (1) {
  [0]=>
  int(1)
}
output at 15:
object(stdClass)#2 (2) {
  [0]=>
  int(1)
  [1]=>
  int(2)
}
