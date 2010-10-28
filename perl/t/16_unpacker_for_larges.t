use strict;
use Test::More;
use Data::MessagePack;

foreach my $data("abc") {
    my $packed = Data::MessagePack->pack($data);

    my $unpacker = Data::MessagePack::Unpacker->new;
    note "buff: ", join " ", map { unpack 'H2', $_ } split //, $packed;

    my $offset = 0;
    foreach my $byte(split //, $packed) {
        note "offset: $offset";
        $offset += $unpacker->execute($byte);
    }

    ok $unpacker->is_finished, 'finished';
    is_deeply $unpacker->data, $data, 'data';
}

done_testing;

