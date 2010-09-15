use strict;
use warnings;
use Data::MessagePack;
use Test::More tests => 6;

my $input = [42, "foo", { x => [ (undef)x16 ] }, 3.14 ];
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
    my $offset = 0;
    my $size   = 5;

    note "length: ", length($packed);
    while(not $up->is_finished) {
        note "offset: ", $offset;
        my $bytes = substr($packed, $offset, $size);
        note join " ", map { unpack 'H2', $_ } split //, $bytes;
        my $x = $up->execute($bytes, 0);
        if($x <= 0) {
            diag "Something's wrong: $x";
            last;
         }
         else {
            $offset += $x;
         }
    }
    ok $up->is_finished;
    is_deeply $up->data, $input;
}

