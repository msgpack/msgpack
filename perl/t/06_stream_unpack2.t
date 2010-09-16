use strict;
use warnings;
use Data::MessagePack;
use Test::More tests => 9;

my $input = [ 42, "foo", { x => [ (1) x 16 ] }, undef, 1 ];
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
    ok !$up->is_finished;
    $up->execute($packed, 3);
    ok $up->is_finished;
    is_deeply $up->data, $input;
}


{
    my $up = Data::MessagePack::Unpacker->new();
    my $size = 8;

    note "packed size: ", length($packed);
    open my $stream, '<:bytes :scalar', \$packed;
    binmode $stream;
    my $buff;
    while( read($stream, $buff, $size) ) {
        note "buff: ", join " ", map { unpack 'H2', $_ } split //, $buff;

        $up->execute($buff);
    }
    ok $up->is_finished, 'is_finished';
    my $data = $up->data;
    note explain($data);
    is_deeply $data, $input;
}

