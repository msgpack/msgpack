--TEST--
Test msgpack_pack() function : basic functionality
--SKIPIF--
<?php if (!extension_loaded("msgpack")) print "skip"; ?>
--FILE--
<?php 
echo "*** Testing msgpack_pack() : basic functionality ***\n";


function create_map($num)
{
    $data = array();
    for($i=0; $i<=$num; $i++)
        $data[$i+1] = $i;
    return $data;
}

$inputs =  array (
        // null
/*1*/   null,
        NULL,

        // boolean
/*3*/   false,
        FALSE,
        true,
        TRUE,

        // zero
/*7*/   0,

        // positive fixnum
/*8*/   1,
        (1<<6),
        (1<<7)-1,

        // positive int 8
/*11*/  (1<<7),
        (1<<8)-1,

        // positive int 16
/*13*/  (1<<8),
        (1<<16)-1,

        // positive int 32
/*15*/  (1<<16),
        (1<<32)-1,

        // positive int 64
/*17*/  (1<<32),
        (1<<64)-1,

        // negative fixnum
/*19*/  -1,
        -((1<<5)-1),
        -(1<<5),

        // negative int 8
/*22*/  -((1<<5)+1),
        -(1<<7),

        // negative int 16
/*24*/  -((1<<7)+1),
        -(1<<15),

        //negative int 32
/*26*/  -((1<<15)+1),
        -(1<<31),

        // negative int 64
/*28*/  -((1<<31)+1),
        -(1<<63),

        // double
/*30*/  1.0,
        0.1,
        -0.1,
        -1.0,

        // fixraw
/*34*/  "",
        str_repeat(" ", (1<<5)-1),

        // raw 16
/*36*/  str_repeat(" ", (1<<5)),
        //str_repeat(" ", (1<<16)-1),

        // raw 32
/*38*/  //str_repeat(" ", (1<<16)),
        //str_repeat(" ", (1<<32)-1),  // memory error

        // fixarraw
/*39*/  array(), 
        range(0, (1<<4)-1),

        // array 16
/*41*/  range(0, (1<<4)),
        //range(0, (1<<16)-1),

        // array 32
/*43*/  //range(0, (1<<16)),
        //range(0, (1<<32)-1),  // memory error

        // fixmap
        //array(),
/*44*/  //create_map((1<<4)-1),

        // map 16
/*45*/  //create_map((1<<4)),
        //create_map((1<<16)-1),

        // map 32
/*47*/  //create_map((1<<16))
        //create_map((1<<32)-1)  // memory error
);

$count = 1;
foreach($inputs as $input) {
  echo "-- Iteration $count --\n";	
  $str = unpack('H*', msgpack_pack($input)); 
  var_dump("0x".$str[1]);
  $count ++;
}

?>
===DONE===
--EXPECT--
*** Testing msgpack_pack() : basic functionality ***
-- Iteration 1 --
string(4) "0xc0"
-- Iteration 2 --
string(4) "0xc0"
-- Iteration 3 --
string(4) "0xc2"
-- Iteration 4 --
string(4) "0xc2"
-- Iteration 5 --
string(4) "0xc3"
-- Iteration 6 --
string(4) "0xc3"
-- Iteration 7 --
string(4) "0x00"
-- Iteration 8 --
string(4) "0x7f"
-- Iteration 9 --
string(6) "0xcc80"
-- Iteration 10 --
string(8) "0xcd0100"
-- Iteration 11 --
string(4) "0xff"
-- Iteration 12 --
string(6) "0xd0df"
-- Iteration 13 --
string(8) "0xd1ff7f"
-- Iteration 14 --
string(8) "0x810101"
-- Iteration 15 --
string(20) "0xcb3ff0000000000000"
-- Iteration 16 --
string(4) "0x90"
-- Iteration 17 --
string(34) "0x9f000102030405060708090a0b0c0d0e"
-- Iteration 18 --
string(40) "0xdc0010000102030405060708090a0b0c0d0e0f"
-- Iteration 19 --
string(64) "0x8f0100020103020403050406050706080709080a090b0a0c0b0d0c0e0d0f0e"
-- Iteration 20 --
string(72) "0xde00100100020103020403050406050706080709080a090b0a0c0b0d0c0e0d0f0e100f"
===DONE===
