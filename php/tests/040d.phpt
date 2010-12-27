--TEST--
broken random data test : MessagePackUnpacker::execute
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

error_reporting(E_ERROR | E_PARSE);

function test() {
    $serialized = msgpack_serialize(null);
    $serialized = substr($serialized, 0, -1);

    $length = mt_rand(1, 255);
    for ($i = 0; $i < $length; ++$i) {
        $serialized .= chr(mt_rand(0, 255));
    }

    // if returned null everything is OK
    $unpacker = new MessagePackUnpacker();
    if ($unpacker->execute($serialized, $offset))
    {
        if (($unserialized = $unpacker->data()) === null) {
            return true;
        }
        $unpacker->reset();
    }
    else
    {
        return true;
    }

    // whole data is read?
    if ($serialized !== msgpack_serialize($unserialized)) {
        return true;
    }

    echo bin2hex($serialized), "\n";
    var_dump($unserialized);

    return false;
}

mt_srand(0x4c05b583);
for ($i = 0; $i < 100; ++$i) {
    if (!test()) break;
}

?>
--EXPECT--
