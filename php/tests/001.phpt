--TEST--
Check for msgpack presence
--SKIPIF--
<?php if (!extension_loaded("msgpack")) print "skip"; ?>
--FILE--
<?php 
echo "msgpack extension is available";
?>
--EXPECT--
msgpack extension is available
