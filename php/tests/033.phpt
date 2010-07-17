--TEST--
Object test, cyclic references
--SKIPIF--
--FILE--
<?php
if(!extension_loaded('msgpack')) {
    dl('msgpack.' . PHP_SHLIB_SUFFIX);
}

class Foo {
    public $parent;
    public $children;

    public function __construct() {
        $this->parent = null;
        $this->children = array();
    }

    public function addChild(Foo $obj) {
        $this->children[] = $obj;
        $obj->setParent($this);
    }

    public function setParent(Foo $obj) {
        $this->parent = $obj;
    }
}

$obj1 = new Foo();

for ($i = 0; $i < 10; $i++) {
    $obj = new Foo();
    $obj1->addChild($obj);
}

$o = msgpack_unserialize(msgpack_serialize($obj1->children));

foreach ($obj1->children as $k => $v) {
    $obj_v = $v;
    $o_v = $o[$k];

    echo gettype($obj_v), "  ", gettype($o_v), PHP_EOL;
}
?>
--EXPECT--
object  object
object  object
object  object
object  object
object  object
object  object
object  object
object  object
object  object
object  object
