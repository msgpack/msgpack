--TEST--
unpack of template converter: multiple class: class unpacker (array: object)
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

$ary = array($obj);

$tpl = array("MyObj");

test("recursive object with object list /w instance", $ary, $tpl, $ary);

--EXPECTF--
array(1) {
  [0]=>
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
}
OK
