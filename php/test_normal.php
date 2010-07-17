<?php
 //$data = array(array(null=>1), array("takei"=>"hide"), 3);
 //$data = array("more"=>10, "test", null);
 //$data = array();
 $data = array(0=>1,1=>2,2=>3);
 var_dump($data);

 // serialize
 $msg = msgpack_pack($data);

 // hexadecimal
 $str = unpack('H*', $msg);
 var_dump("0x".$str[1]);

 // deserialize
 $ret = msgpack_unpack($msg);
 var_dump($ret);
?>

