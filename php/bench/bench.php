<?php

//ini_set('memory_limit' ,'128M');

$ary = array();
for($i=0; $i<pow(2, 10); $i++){
    $ary = array_merge($ary, range(0, 1024));
}

echo count($ary);

function getSize($ary)
{
    if (ini_get('mbstring.func_overload') & 2 && function_exists('mb_strlen')) {
        $size = mb_strlen($ary, 'ASCII');
    } else {
        $size = strlen($ary);
    }

    return $size;
}

echo "fin" . $size . "\n";

echo "----\n";
echo "MessagePack\n";
$a = microtime(true);
$packed = msgpack_pack($ary);
$b = microtime(true);
echo ($b-$a) . "sec, " . getSize($packed) . "bytes\n";

$a = microtime(true);
$pack = msgpack_unpack($packed);
$b = microtime(true);
echo ($b-$a) . "sec\n";


echo "----\n";
echo "JSON\n";
$a = microtime(true);
$jsoned = json_encode($ary);
$b = microtime(true);
echo ($b-$a) . "sec, " . getSize($jsoned) . "bytes\n";

$a = microtime(true);
$json = json_decode($jsoned);
$b = microtime(true);
echo ($b-$a) . "sec\n";


?>
