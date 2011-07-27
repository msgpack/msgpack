--TEST--
Unserialize invalid random data
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

foreach ($datas as $data)
{
    $str = msgpack_serialize($data);
    $len = strlen($str);

    for ($j = 0; $j < 200; $j++)
    {
        for ($i = 0; $i < $len - 1; $i++)
        {
            $sub = substr($str, 0, $i);
            $sub .= mcrypt_create_iv(30, MCRYPT_DEV_URANDOM);
            $php_errormsg = null;
            $v = msgpack_unserialize($sub);
        }
    }
}

--EXPECT--
