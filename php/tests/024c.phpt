--TEST--
Recursive objects
--SKIPIF--
<?php
if (version_compare(PHP_VERSION, '5.2.0') >= 0) {
    echo "skip tests in PHP 5.1 or older";
}
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

function test($type, $variable, $test) {
    $serialized = msgpack_serialize($variable);
    $unserialized = msgpack_unserialize($serialized);

    echo $type, PHP_EOL;
    echo bin2hex($serialized), PHP_EOL;
    var_dump($unserialized);
    echo $test || $unserialized == $variable ? 'OK' : 'ERROR', PHP_EOL;
}

class Obj {
    public $a;
    protected $b;
    private $c;

    function __construct($a, $b, $c) {
        $this->a = $a;
        $this->b = $b;
        $this->c = $c;
    }
}

class Obj2 {
    public $aa;
    protected $bb;
    private $cc;
    private $obj;

    function __construct($a, $b, $c) {
        $this->a = $a;
        $this->b = $b;
        $this->c = $c;

        $this->obj = new Obj($a, $b, $c);
    }
}

class Obj3 {
    private $objs;

    function __construct($a, $b, $c) {
        $this->objs = array();

        for ($i = $a; $i < $c; $i += $b) {
            $this->objs[] = new Obj($a, $i, $c);
        }
    }
}

class Obj4 {
    private $a;
    private $obj;

    function __construct($a) {
        $this->a = $a;
    }

    public function set($obj) {
        $this->obj = $obj;
    }
}

$o2 = new Obj2(1, 2, 3);
test('objectrec', $o2, false);

$o3 = new Obj3(0, 1, 4);
test('objectrecarr', $o3, false);

$o4 = new Obj4(100);
$o4->set($o4);
test('objectselfrec', $o4, true);
?>
--EXPECTF--
objectrec
88c0a44f626a32a26161c0a5002a006262c0a8004f626a32006363c0a9004f626a32006f626a84c0a34f626aa16101a4002a006202a6004f626a006303a16101a16202a16303
object(Obj2)#%d (7) {
  ["aa"]=>
  NULL
  ["bb:protected"]=>
  NULL
  ["cc:private"]=>
  NULL
  ["obj:private"]=>
  object(Obj)#%d (3) {
    ["a"]=>
    int(1)
    ["b:protected"]=>
    int(2)
    ["c:private"]=>
    int(3)
  }
  ["a"]=>
  int(1)
  ["b"]=>
  int(2)
  ["c"]=>
  int(3)
}
OK
objectrecarr
82c0a44f626a33aa004f626a33006f626a739484c0a34f626aa16100a4002a006200a6004f626a00630484c0a34f626aa16100a4002a006201a6004f626a00630484c0a34f626aa16100a4002a006202a6004f626a00630484c0a34f626aa16100a4002a006203a6004f626a006304
object(Obj3)#%d (1) {
  ["objs:private"]=>
  array(4) {
    [0]=>
    object(Obj)#%d (3) {
      ["a"]=>
      int(0)
      ["b:protected"]=>
      int(0)
      ["c:private"]=>
      int(4)
    }
    [1]=>
    object(Obj)#%d (3) {
      ["a"]=>
      int(0)
      ["b:protected"]=>
      int(1)
      ["c:private"]=>
      int(4)
    }
    [2]=>
    object(Obj)#%d (3) {
      ["a"]=>
      int(0)
      ["b:protected"]=>
      int(2)
      ["c:private"]=>
      int(4)
    }
    [3]=>
    object(Obj)#%d (3) {
      ["a"]=>
      int(0)
      ["b:protected"]=>
      int(3)
      ["c:private"]=>
      int(4)
    }
  }
}
OK
objectselfrec
83c0a44f626a34a7004f626a34006164a9004f626a34006f626a82c0040001
object(Obj4)#%d (2) {
  ["a:private"]=>
  int(100)
  ["obj:private"]=>
  object(Obj4)#%d (2) {
    ["a:private"]=>
    int(100)
    ["obj:private"]=>
    *RECURSION*
  }
}
OK
