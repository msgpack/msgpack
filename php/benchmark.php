<?php
require_once 'Benchmark/Timer.php';

$loop = 10000;
$retry = 10;
$value_display = false;

$types = array(
    1, //integer
    2, //float
    3, //string
    4, //array
    5, //hash
    6, //object
);

foreach ($types as $type)
{
    switch ($type)
    {
        case 1:
            //integer
            $value = rand();
            break;
        case 2:
            //float
            $value = log(rand());
            break;
        case 3:
            //string
            $value = md5(rand());
            break;
        case 4:
            //array
            $value = array(md5(rand()),
                           md5(rand()),
                           md5(rand()),
                           md5(rand()),
                           md5(rand()));
            break;
        case 5:
            //hash
            $value = array(md5(rand()) => md5(rand()),
                           md5(rand()) => md5(rand()),
                           md5(rand()) => md5(rand()),
                           md5(rand()) => md5(rand()),
                           md5(rand()) => md5(rand()));
            break;
        case 6:
            //object
            $value = new stdClass;
            $value->param1 = rand();
            $value->param2 = md5(uniqid());
            $value->param3 = array(md5(uniqid()));
            $value->param4 = array(md5(uniqid()) => md5(uniqid()));
            $value->param5 = null;
            break;
        default:
            //null
            $value = null;
    }

    if (!is_numeric($retry) || empty($retry))
    {
        $retry = 1;
    }

    $serialize_pack = 0;
    $serialize_unpack = 0;
    $serialize_size = 0;
    $serialize_status = '*NG*';
    $json_pack = 0;
    $json_unpack = 0;
    $json_size = 0;
    $json_status = '*NG*';
    $igbinary_pack = 0;
    $igbinary_unpack = 0;
    $igbinary_size = 0;
    $igbinary_status = '*NG*';
    $msgpack_pack = 0;
    $msgpack_unpack = 0;
    $msgpack_size = 0;
    $msgpack_status = '*NG*';

    for ($c = 0; $c < $retry; $c++)
    {
        //default (serialize)
        $pack = null;
        $unpack = null;
        $t = new Benchmark_Timer;
        $t->start();
        for ($i = 0; $i < $loop; $i++)
        {
            $pack = serialize($value);
        }
        $t->setMarker('serialize');
        for ($i = 0; $i < $loop; $i++)
        {
            $unpack = unserialize($pack);
        }
        $t->stop();
        //$t->display();
        $profiling = $t->getProfiling();
        unset($t);

        $serialize_pack += $profiling[1]['diff'];
        $serialize_unpack += $profiling[2]['diff'];
        $serialize_size += strlen($pack);
        if ($unpack === $value ||
            (is_object($value) && $unpack == $value))
        {
            $serialize_status = 'OK';
        }

        //json
        $pack = null;
        $unpack = null;
        $opt = false;
        if (is_array($value))
        {
            $opt = true;
        }
        $t = new Benchmark_Timer;
        $t->start();
        for ($i = 0; $i < $loop; $i++)
        {
            $pack = json_encode($value);
        }
        $t->setMarker('json_encode');
        for ($i = 0; $i < $loop; $i++)
        {
            $unpack = json_decode($pack, $opt);
        }
        $t->stop();
        //$t->display();
        $profiling = $t->getProfiling();
        unset($t);

        $json_pack += $profiling[1]['diff'];
        $json_unpack += $profiling[2]['diff'];
        $json_size += strlen($pack);
        if ($unpack === $value ||
            (is_object($value) && $unpack == $value) ||
            (is_float($value) &&
             number_format($value, 10, '.', '') ===
             number_format($unpack, 10, '.', '')))
        {
            $json_status = 'OK';
        }

        //igbinary
        if (extension_loaded('igbinary'))
        {
            $pack = null;
            $unpack = null;
            $t = new Benchmark_Timer;
            $t->start();
            for ($i = 0; $i < $loop; $i++)
            {
                $pack = igbinary_serialize($value);
            }
            $t->setMarker('igbinary_serialize');
            for ($i = 0; $i < $loop; $i++)
            {
                $unpack = igbinary_unserialize($pack);
            }
            $t->stop();
            //$t->display();
            $profiling = $t->getProfiling();
            unset($t);

            $igbinary_pack += $profiling[1]['diff'];
            $igbinary_unpack += $profiling[2]['diff'];
            $igbinary_size += strlen($pack);
            if ($unpack === $value ||
                (is_object($value) && $unpack == $value))
            {
                $igbinary_status = 'OK';
            }
        }

        //msgpack
        $pack = null;
        $unpack = null;
        $t = new Benchmark_Timer;
        $t->start();
        for ($i = 0; $i < $loop; $i++)
        {
            $pack = msgpack_serialize($value);
        }
        $t->setMarker('msgpack_serialize');
        for ($i = 0; $i < $loop; $i++)
        {
            $unpack = msgpack_unserialize($pack);
        }
        $t->stop();
        //$t->display();
        $profiling = $t->getProfiling();
        unset($t);

        $msgpack_pack += $profiling[1]['diff'];
        $msgpack_unpack += $profiling[2]['diff'];
        $msgpack_size += strlen($pack);
        if ($unpack === $value ||
            (is_object($value) && $unpack == $value))
        {
            $msgpack_status = 'OK';
        }
    }

    $serialize_pack /= $retry;
    $serialize_unpack /= $retry;
    $serialize_size /= $retry;
    $json_pack /= $retry;
    $json_unpack /= $retry;
    $json_size /= $retry;
    $igbinary_pack /= $retry;
    $igbinary_unpack /= $retry;
    $igbinary_size /= $retry;
    $msgpack_pack /= $retry;
    $msgpack_unpack /= $retry;
    $msgpack_size /= $retry;

    printf("[%-10s] %13s %13s %13s %13s\n",
           gettype($value), 'default', 'json', 'igbinary', 'msgpack');
    printf("status     : %12s  %12s  %12s  %12s\n",
           $serialize_status, $json_status, $igbinary_status, $msgpack_status);
    printf("serialize  : %.4f (100%%) %.4f (%3d%%) %.4f (%3d%%) %.4f (%3d%%)\n",
           $serialize_pack,
           $json_pack, ($json_pack / $serialize_pack * 100),
           $igbinary_pack, ($igbinary_pack / $serialize_pack * 100),
           $msgpack_pack, ($msgpack_pack / $serialize_pack * 100));
    printf("unserialize: %.4f (100%%) %.4f (%3d%%) %.4f (%3d%%) %.4f (%3d%%)\n",
           $serialize_unpack,
           $json_unpack, ($json_unpack / $serialize_unpack * 100),
           $igbinary_unpack, ($igbinary_unpack / $serialize_unpack * 100),
           $msgpack_unpack, ($msgpack_unpack / $serialize_unpack * 100));
    printf("size       : %6d (100%%) %6d (%3d%%) %6d (%3d%%) %6d (%3d%%)\n\n",
           $serialize_size,
           $json_size, ($json_size / $serialize_size * 100),
           $igbinary_size, ($igbinary_size / $serialize_size * 100),
           $msgpack_size, ($msgpack_size / $serialize_size * 100));
    if ($value_display === true)
    {
        var_dump($value);
        echo PHP_EOL;
    }
}
