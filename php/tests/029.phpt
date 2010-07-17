--TEST--
Msgpack module info
--SKIPIF--
<?php if (!extension_loaded("msgpack")) print "skip"; ?>
--FILE--
<?php 
ob_start();
phpinfo(INFO_MODULES);
$str = ob_get_clean();

$array = explode("\n", $str);
$array = preg_grep('/^msgpack/', $array);

echo implode("\n", $array), PHP_EOL;

--EXPECTF--
msgpack
msgpack support => enabled
msgpack version => %s
msgpack Session Support => enabled
