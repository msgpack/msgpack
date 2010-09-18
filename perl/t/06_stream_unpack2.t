use strict;
use warnings;
use Data::MessagePack;
use Test::More tests => 9;
use t::Util;

my $input = [
    false,true,null,0,0,0,0,0,0,0,0,0,-1,-1,-1,-1,-1,
    127,127,255,65535,4294967295,-32,-32,-128,-32768,
    -2147483648,0.0,-0.0,1.0,-1.0,"a","a","a","","","",
    [0],[0],[0],[],[],[],{},{},{},
    {"a" => 97},{"a" => 97},{"a" => 97},[[]],[["a"]]
];

my $packed = Data::MessagePack->pack($input);
is_deeply(Data::MessagePack->unpack($packed), $input);

{
    my $up = Data::MessagePack::Unpacker->new();
    $up->execute($packed, 0);
    ok $up->is_finished;
    is_deeply $up->data, $input;
}

{
    my $up = Data::MessagePack::Unpacker->new();
    $packed x= 3;

    my $offset = 0;
    for my $i(1 .. 3) {
        note "block $i (offset: $offset/".length($packed).")";
        note "starting 3 bytes: ", join " ", map { unpack 'H2', $_ }
            split //, substr($packed, $offset, 3);

        $offset = $up->execute($packed, $offset);
        ok $up->is_finished, 'finished';
        my $data = $up->data;
        is_deeply $data, $input;
        $up->reset();
    }
}


