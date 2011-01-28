--TEST--
unpack of object converter : class unpack (object)
--SKIPIF--
<?php
if (version_compare(PHP_VERSION, '5.2.0') < 0) {
    echo "skip tests in PHP 5.2 or newer";
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

$object = new Obj();

test('null', null, new Obj(), new Obj(null, null, null));

test('bool: true', true, new Obj(), new Obj(true, null, null));
test('bool: false', false, new Obj(), new Obj(false, null, null));

test('zero: 0', 0, new Obj(), new Obj(0, null, null));
test('small: 1', 1, new Obj(), new Obj(1, null, null));
test('small: -1', -1, new Obj(), new Obj(-1, null, null));
test('medium: 1000', 1000, new Obj(), new Obj(1000, null, null));
test('medium: -1000', -1000, new Obj(), new Obj(-1000, null, null));
test('large: 100000', 100000, new Obj(), new Obj(100000, null, null));
test('large: -100000', -100000, new Obj(), new Obj(-100000, null, null));

test('double: 123.456', 123.456, new Obj(), new Obj(123.456, null, null));

test('empty: ""', "", new Obj(), new Obj("", null, null));
test('string: "foobar"', "foobar", new Obj(), new Obj("foobar", null, null));

test('array: empty', array(), new Obj(), new Obj(null, null, null));
test('array(1, 2, 3)', array(1, 2, 3), new Obj(), new Obj(1, 2, 3));
test('array(array(1, 2, 3), arr...', array(array(1, 2, 3), array(4, 5, 6), array(7, 8, 9)), new Obj(), new Obj(array(1, 2, 3), array(4, 5, 6), array(7, 8, 9)));
test('array(1, 2, 3, 4)', array(1, 2, 3, 4), new Obj());

test('array("foo", "foobar", "foohoge")', array("foo", "foobar", "hoge"), new Obj(), new Obj("foo", "foobar", "hoge"));
test('array("a" => 1, "b" => 2))', array("a" => 1, "b" => 2), new Obj(), new Obj(1, 2, null));
test('array("one" => 1, "two" => 2))', array("one" => 1, "two" => 2), new Obj(), new Obj(null, null, null, array("one" => 1, "two" => 2)));
test('array("" => "empty")', array("" => "empty"), new Obj());

test('array("a" => 1, "b" => 2, 3))', array("a" => 1, "b" => 2, 3), new Obj(), new Obj(1, 2, 3));
test('array(3, "a" => 1, "b" => 2))', array(3, "a" => 1, "b" => 2), new Obj(), new Obj(1, 2, 3));
test('array("a" => 1, 3, "b" => 2))', array("a" => 1, 3, "b" => 2), new Obj(), new Obj(1, 2, 3));

$a = array('foo');
test('array($a, $a)', array($a, $a), new Obj(), new Obj($a, $a, null));
test('array(&$a, &$a)', array(&$a, &$a), new Obj(), new Obj($a, $a, null));

test('array(&$a, $a)', array($a, &$a), new Obj(), new Obj($a, $a, null));
test('array(&$a, $a)', array(&$a, $a), new Obj(), new Obj($a, $a, null));

$a = array(
    'a' => array(
        'b' => 'c',
        'd' => 'e'
        ),
    'f' => array(
        'g' => 'h'
        )
    );
test('array', $a, new Obj(), new Obj(null, null, null, $a));

$o = new Obj(1, 2, 3);
test('object', $o, new Obj(), new Obj(1, 2, 3));

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
test('object', $o, new Obj(), new Obj($o));

$o1 = new Obj2(1, 2, 3);
$o2 = new Obj2(4, 5, 6);
test('object', array($o1, $o2), new Obj(), new Obj($o1, $o2));

$o = new Obj2(1, 2, 3);
test('object', array(&$o, &$o), new Obj(), new Obj($o, $o));

$o = new Obj2(1, 2, 3);
test('object', array(&$o, $o), new Obj(), new Obj($o, $o));

$o = new Obj2(1, 2, 3);
test('object', array($o, &$o), new Obj(), new Obj($o, $o));

--EXPECTF--
object(Obj)#%d (3) {
  ["a"]=>
  NULL
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  bool(true)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  bool(false)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(0)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(-1)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1000)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(-1000)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(100000)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(-100000)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  float(123.456)
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  string(0) ""
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  string(6) "foobar"
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  NULL
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
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
  [%r"?b"?:protected"?%r]=>
  array(3) {
    [0]=>
    int(4)
    [1]=>
    int(5)
    [2]=>
    int(6)
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
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
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
  int(3)
  [3]=>
  int(4)
}
SKIP
object(Obj)#%d (3) {
  ["a"]=>
  string(3) "foo"
  [%r"?b"?:protected"?%r]=>
  string(6) "foobar"
  [%r"?c"?:("Obj":)?private"?%r]=>
  string(4) "hoge"
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (5) {
  ["a"]=>
  NULL
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
  ["one"]=>
  int(1)
  ["two"]=>
  int(2)
}
OK
object(Obj)#%d (4) {
  ["a"]=>
  NULL
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
  [""]=>
  string(5) "empty"
}
SKIP
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  int(1)
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?b"?:protected"?%r]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  &array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?b"?:protected"?%r]=>
  &array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?b"?:protected"?%r]=>
  &array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  &array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?b"?:protected"?%r]=>
  array(1) {
    [0]=>
    string(3) "foo"
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
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
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
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
  [%r"?b"?:protected"?%r]=>
  int(2)
  [%r"?c"?:("Obj":)?private"?%r]=>
  int(3)
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?b"?:protected"?%r]=>
  NULL
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?b"?:protected"?%r]=>
  object(Obj2)#%d (3) {
    ["A"]=>
    int(4)
    [%r"?B"?:protected"?%r]=>
    int(5)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(6)
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  &object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?b"?:protected"?%r]=>
  &object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?b"?:protected"?%r]=>
  object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
object(Obj)#%d (3) {
  ["a"]=>
  &object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?b"?:protected"?%r]=>
  &object(Obj2)#%d (3) {
    ["A"]=>
    int(1)
    [%r"?B"?:protected"?%r]=>
    int(2)
    [%r"?C"?:("Obj2":)?private"?%r]=>
    int(3)
  }
  [%r"?c"?:("Obj":)?private"?%r]=>
  NULL
}
OK
