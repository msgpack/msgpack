--TEST--
unpack of template converter: multiple class/variable: class unpacker (array: string)
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
        $this->subary = array(new SubObj());
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

$obj0 = new MyObj();
$obj0->pdata = "pubdata0";
$obj0->subary[0]->subpdata = "subpubdata00";
$subobj01 = new SubObj();
$subobj01->subpdata = "subpdata01";
$obj0->subary[1] = $subobj01;
$obj1 = new MyObj();
$obj1->pdata = "pubdata1";
$obj1->subary[0]->subpdata = "subpubdata1";
$subobj11 = new SubObj();
$subobj11->subpdata = "subpdata11";
$obj1->subary[1] = $subobj11;

$ary = array($obj0, $obj1);

$tpl = array("MyObj");

test("recursive object list with object list /w string", $ary, $tpl, $ary);

--EXPECTF--
array(2) {
  [0]=>
  object(MyObj)#%d (4) {
    ["data:private"]=>
    string(8) "datadata"
    ["priv:private"]=>
    string(8) "privdata"
    ["pdata"]=>
    string(8) "pubdata0"
    ["subary"]=>
    array(2) {
      [0]=>
      object(SubObj)#%d (3) {
        ["subdata:private"]=>
        string(11) "subdatadata"
        ["subpriv:private"]=>
        string(11) "subprivdata"
        ["subpdata"]=>
        string(12) "subpubdata00"
      }
      [1]=>
      object(SubObj)#%d (3) {
        ["subdata:private"]=>
        string(11) "subdatadata"
        ["subpriv:private"]=>
        string(11) "subprivdata"
        ["subpdata"]=>
        string(10) "subpdata01"
      }
    }
  }
  [1]=>
  object(MyObj)#%d (4) {
    ["data:private"]=>
    string(8) "datadata"
    ["priv:private"]=>
    string(8) "privdata"
    ["pdata"]=>
    string(8) "pubdata1"
    ["subary"]=>
    array(2) {
      [0]=>
      object(SubObj)#%d (3) {
        ["subdata:private"]=>
        string(11) "subdatadata"
        ["subpriv:private"]=>
        string(11) "subprivdata"
        ["subpdata"]=>
        string(11) "subpubdata1"
      }
      [1]=>
      object(SubObj)#%d (3) {
        ["subdata:private"]=>
        string(11) "subdatadata"
        ["subpriv:private"]=>
        string(11) "subprivdata"
        ["subpdata"]=>
        string(10) "subpdata11"
      }
    }
  }
}
OK
