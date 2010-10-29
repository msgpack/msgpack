use strict;
use Test::More;
use Data::MessagePack;

foreach my $data("abc", [ 'x' x 1024 ], [0xFFFF42]) {
    my $packed = Data::MessagePack->pack($data);

    my $unpacker = Data::MessagePack::Unpacker->new;
    note "buff: ", join " ", map { unpack 'H2', $_ } split //, $packed;

    foreach my $byte(split //, $packed) {
        $unpacker->execute($byte);
    }

    ok $unpacker->is_finished, 'finished';
    is_deeply $unpacker->data, $data, 'data';
}

done_testing;

