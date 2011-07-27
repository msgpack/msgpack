--TEST--
unpack of template converter: class unpacker (array: string: OPT_PHPONLY=false)
--SKIPIF--
<?php
if (version_compare(PHP_VERSION, '5.2.0') >= 0) {
    echo "skip tests in PHP 5.1 or older";
}
--FILE--
<?php
if(!extension_loaded('msgpack'))
{
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

//error_reporting(0);

function test($type, $variable, $object, $result = null)
{
    $msgpack = new MessagePack();
    if (version_compare(PHP_VERSION, '5.1.0') <= 0)
    {
        $msgpack->setOption(MESSAGEPACK_OPT_PHPONLY, false);
    }
    else
    {
        $msgpack->setOption(MessagePack::OPT_PHPONLY, false);
    }

    $serialized = $msgpack->pack($variable);

    $unserialized = $msgpack->unpack($serialized, $object);

    var_dump($unserialized);
    if ($result)
    {
        echo $unserialized == $result ? 'OK' : 'ERROR', PHP_EOL;
    }
    else
    {
        echo 'SKIP', PHP_EOL;
    }
}

class MyObj
{
    private $data = null;
    private $priv = "privdata";
    public  $pdata = null;

    function __construct()
    {
        $this->data = "datadata";
    }
}

$obj = new MyObj();
$obj->pdata = "pubdata0";

$obj2 = new MyObj();
$obj2->pdata = "pubdata1";

$ary = array($obj, $obj2);

$tpl = array("MyObj");

test("object list /w string", $ary, $tpl, $ary);

--EXPECTF--
array(2) {
  [0]=>
  object(MyObj)#%d (3) {
    ["data:private"]=>
    string(8) "datadata"
    ["priv:private"]=>
    string(8) "privdata"
    ["pdata"]=>
    string(8) "pubdata0"
  }
  [1]=>
  object(MyObj)#%d (3) {
    ["data:private"]=>
    string(8) "datadata"
    ["priv:private"]=>
    string(8) "privdata"
    ["pdata"]=>
    string(8) "pubdata1"
  }
}
OK
