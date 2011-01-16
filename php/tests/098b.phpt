--TEST--
unpack of object converter: class unpack (string: OPT_PHPONLY=false)
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

class Obj
{
    public $a;
    protected $b;
    private $c;

    public function __construct($a = null, $b = null, $c = null, $d = null)
    {
        $this->a = $a;
        $this->b = $b;
        $this->c = $c;
        if (is_array($d))
        {
            foreach ($d as $key => $val)
            {
                $this->{$key} = $val;
            }
        }
    }
}

test('null', null, 'Obj', new Obj(null, null, null));

test('bool: true', true, 'Obj', new Obj(true, null, null));
test('bool: false', false, 'Obj', new Obj(false, null, null));

test('zero: 0', 0, 'Obj', new Obj(0, null, null));
test('small: 1', 1, 'Obj', new Obj(1, null, null));
test('small: -1', -1, 'Obj', new Obj(-1, null, null));
test('medium: 1000', 1000, 'Obj', new Obj(1000, null, null));
test('medium: -1000', -1000, 'Obj', new Obj(-1000, null, null));
test('large: 100000', 100000, 'Obj', new Obj(100000, null, null));
test('large: -100000', -100000, 'Obj', new Obj(-100000, null, null));

test('double: 123.456', 123.456, 'Obj', new Obj(123.456, null, null));

test('empty: ""', "", 'Obj', new Obj("", null, null));
test('string: "foobar"', "foobar", 'Obj', new Obj("foobar", null, null));

test('array: empty', array(), 'Obj', new Obj(null, null, null));
test('array(1, 2, 3)', array(1, 2, 3), 'Obj', new Obj(1, 2, 3));
test('array(array(1, 2, 3), arr...', array(array(1, 2, 3), array(4, 5, 6), array(7, 8, 9)), 'Obj', new Obj(array(1, 2, 3), array(4, 5, 6), array(7, 8, 9)));
test('array(1, 2, 3, 4)', array(1, 2, 3, 4), 'Obj');

test('array("foo", "foobar", "foohoge")', array("foo", "foobar", "hoge"), 'Obj', new Obj("foo", "foobar", "hoge"));
test('array("a" => 1, "b" => 2))', array("a" => 1, "b" => 2), 'Obj', new Obj(1, 2, null));
test('array("one" => 1, "two" => 2))', array("one" => 1, "two" => 2), 'Obj', new Obj(null, null, null, array("one" => 1, "two" => 2)));

test('array("a" => 1, "b" => 2, 3))', array("a" => 1, "b" => 2, 3), 'Obj', new Obj(1, 2, 3));
test('array(3, "a" => 1, "b" => 2))', array(3, "a" => 1, "b" => 2), 'Obj', new Obj(1, 2, 3));
test('array("a" => 1, 3, "b" => 2))', array("a" => 1, 3, "b" => 2), 'Obj', new Obj(1, 2, 3));

$a = array('foo');
test('array($a, $a)', array($a, $a), 'Obj', new Obj($a, $a, null));

$a = array(
    'a' => array(
        'b' => 'c',
        'd' => 'e'
        ),
    'f' => array(
        'g' => 'h'
        )
    );
test('array', $a, 'Obj', new Obj(null, null, null, $a));

$o = new Obj(1, 2, 3);
test('object', $o, 'Obj', new Obj(1, 2, 3));

class Obj2 {
    public $A;
    protected $B;
    private $C;

    function __construct($a, $b, $c) {
        $this->A = $a;
        $this->B = $b;
        $this->C = $c;
    }
}

$o = new Obj2(1, 2, 3);
test('object', $o, 'Obj', new Obj(1, 2, 3));

$o1 = new Obj2(1, 2, 3);
$o2 = new Obj2(4, 5, 6);
test('object', array($o1, $o2), 'Obj', new Obj(array(1, 2, 3), array(4, 5, 6)));

--EXPECTF--
object(Obj)#%d (3) {
  ["a"]=>
  NULL
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  bool(true)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  bool(false)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(0)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(-1)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1000)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(-1000)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(100000)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(-100000)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  float(123.456)
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  string(0) ""
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  string(6) "foobar"
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  NULL
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  array(3) {
    [0]=>
    int(1)
    [1]=>
    int(2)
    [2]=>
    int(3)
  }
  ["b:protected"]=>
  array(3) {
    [0]=>
    int(4)
    [1]=>
    int(5)
    [2]=>
    int(6)
  }
  ["c:private"]=>
  array(3) {
    [0]=>
    int(7)
    [1]=>
    int(8)
    [2]=>
    int(9)
  }
}
OK
object(Obj)#%d (4) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  int(3)
  [3]=>
  int(4)
}
SKIP
object(Obj)#%d (3) {
  ["a"]=>
  string(3) "foo"
  ["b:protected"]=>
  string(6) "foobar"
  ["c:private"]=>
  string(4) "hoge"
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (5) {
  ["a"]=>
  NULL
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
  ["one"]=>
  int(1)
  ["two"]=>
  int(2)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
  ["b:protected"]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
  ["c:private"]=>
  NULL
}
OK
object(Obj)#%d (4) {
  ["a"]=>
  array(2) {
    ["b"]=>
    string(1) "c"
    ["d"]=>
    string(1) "e"
  }
  ["b:protected"]=>
  NULL
  ["c:private"]=>
  NULL
  ["f"]=>
  array(1) {
    ["g"]=>
    string(1) "h"
  }
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  ["b:protected"]=>
  int(2)
  ["c:private"]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  array(3) {
    [0]=>
    int(1)
    [1]=>
    int(2)
    [2]=>
    int(3)
  }
  ["b:protected"]=>
  array(3) {
    [0]=>
    int(4)
    [1]=>
    int(5)
    [2]=>
    int(6)
  }
  ["c:private"]=>
  NULL
}
OK
