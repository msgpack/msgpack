use strict;
use warnings;
use Data::MessagePack;
use Test::More tests => 6;

my $input = [(undef)x16];
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
    is $up->execute(substr($packed, 0, 3), 0), 3;
    $up->execute($packed, 3);
    ok $up->is_finished;
    is_deeply $up->data, $input;
}


