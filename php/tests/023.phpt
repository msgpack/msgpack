--TEST--
Resource
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

error_reporting(0);

function test($type, $variable, $test) {
    $serialized = msgpack_serialize($variable);
    $unserialized = msgpack_unserialize($serialized);

    echo $type, PHP_EOL;
    echo bin2hex($serialized), PHP_EOL;
    var_dump($unserialized);
    echo $test || $unserialized === null ? 'OK' : 'FAIL', PHP_EOL;
}

if (function_exists('curl_init')) {
    $test = 'curl';
    $res = curl_init('http://php.net/');
} else {
    $test = 'dir';
    $res = opendir('/tmp');
}

test('resource', $res, false);

switch ($test) {
    case 'curl':
        curl_close($res);
        break;
    default:
        closedir($res);
        break;
}
?>
--EXPECT--
resource
c0
NULL
OK
