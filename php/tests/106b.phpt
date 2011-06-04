--TEST--
unpack of object converter: class unpacker (string: OPT_PHPONLY=false)
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

error_reporting(0);

function test($type, $variable, $object, $result = null)
{
    $msgpack = new MessagePack();
    $msgpack->setOption(MessagePack::OPT_PHPONLY, false);

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

class MyObj {
    private $data = null;
    private $priv = "privdata";
    public  $pdata = null;
    public $subary = null;

    function __construct() {
	$this->data = "datadata";
	$this->subary = new SubObj();
    }
}

class SubObj {
    private $subdata = null;
    private $subpriv = "subprivdata";
    public  $subpdata = null;

    function __construct() {
	$this->subdata = "subdatadata";
    }
}

$obj = new MyObj();
$obj->pdata = "pubdata";
$obj->subary->subpdata = "subpubdata";

$tpl = "MyObj";

test("recursive object /w string", $obj, $tpl, $obj);

--EXPECTF--
object(MyObj)#%d (4) {
  ["data":"MyObj":private]=>
  string(8) "datadata"
  ["priv":"MyObj":private]=>
  string(8) "privdata"
  ["pdata"]=>
  string(7) "pubdata"
  ["subary"]=>
  object(SubObj)#%d (3) {
    ["subdata":"SubObj":private]=>
    string(11) "subdatadata"
    ["subpriv":"SubObj":private]=>
    string(11) "subprivdata"
    ["subpdata"]=>
    string(10) "subpubdata"
  }
}
OK
