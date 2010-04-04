<?php

 // serialized data
 $msgs = array(pack("C*", 0x93, 0x01, 0x02, 0x03, 0x92), pack("C*", 0x03, 0x09, 0x04));

 // streaming deserialize
 $unpacker = new MessagePack();
 $unpacker->initialize();
 $buffer = "";
 $nread = 0;

 foreach($msgs as $msg){
    $buffer = $buffer . $msg;

    while(true){
        $nread = $unpacker->execute($buffer, $nread);

        if($unpacker->finished()){
            $msg = $unpacker->data();
            var_dump($msg);

            $unpacker->initialize();
            $buffer = substr($buffer, $nread);
            $nread = 0;

            if(!empty($buffer)){
                continue;
            }
        }
        break;
    }
 }
?>

