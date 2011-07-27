--TEST--
unpack of template converter: class unpacker (object: OPT_PHPONLY=false)
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
    public $subary = null;

    function __construct()
    {
        $this->data = "datadata";
        $this->subary = new SubObj();
    }
}

class SubObj
{
    private $subdata = null;
    private $subpriv = "subprivdata";
    public  $subpdata = null;

    function __construct()
    {
        $this->subdata = "subdatadata";
    }
}

$obj = new MyObj();
$obj->pdata = "pubdata";
$obj->subary->subpdata = "subpubdata";

$tpl = new MyObj();

test("recursive object /w instance", $obj, $tpl, $obj);

--EXPECTF--
object(MyObj)#%d (4) {
  ["data:private"]=>
  string(8) "datadata"
  ["priv:private"]=>
  string(8) "privdata"
  ["pdata"]=>
  string(7) "pubdata"
  ["subary"]=>
  object(SubObj)#%d (3) {
    ["subdata:private"]=>
    string(11) "subdatadata"
    ["subpriv:private"]=>
    string(11) "subprivdata"
    ["subpdata"]=>
    string(10) "subpubdata"
  }
}
OK
