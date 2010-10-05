--TEST--
Resource
--SKIPIF--
<?php
if (!function_exists("curl_init") && !class_exists("Sqlite3"))) {
    echo "skip";
}
?>
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
    $res = curl_init('http://opensource.dynamoid.com');
} else if (class_exists('Sqlite3')) {
    $test = 'sqlite';
    $sqlite = new Sqlite3();
    $res = $sqlite->open('db.txt');
}

test('resource', $res, false);

switch ($test) {
    case 'curl':
        curl_close($res);
        break;
    case 'sqlite':
        if (isset($sqlite)) {
            $sqlite->close();
        }
        @unlink('db.txt');
        break;
}
?>
--EXPECT--
resource
c0
NULL
OK
