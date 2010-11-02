#!perl

# This feature is not yet supported, but 0.23 (or former) caused SEGV in this code,
# so we put it here.

use strict;
use warnings;
use Data::MessagePack;
use Test::More;
use t::Util;

my $input = [
    false,true,null,0,0,0,0,0,0,0,0,0,-1,-1,-1,-1,-1,
    127,127,255,65535,4294967295,-32,-32,-128,-32768,
    -2147483648,0.0,-0.0,1.0,-1.0,"a","a","a","","","",
    [0],[0],[0],[],[],[],{},{},{},
    {"a" => 97},{"a" => 97},{"a" => 97},[[]],[["a"]]
];

my $packed = Data::MessagePack->pack($input);

foreach my $size(1 .. 16) {
    my $up = Data::MessagePack::Unpacker->new();

    open my $stream, '<:bytes :scalar', \$packed;
    binmode $stream;
    my $buff;
    my $done = 0;
    while( read($stream, $buff, $size) ) {
        note "buff: ", join " ", map { unpack 'H2', $_ } split //, $buff;

        $done = $up->execute($buff);
    }
    is $done, length($packed);
    ok $up->is_finished, "is_finished: $size";
    my $data = $up->data;
    is_deeply $data, $input;
}

done_testing;
