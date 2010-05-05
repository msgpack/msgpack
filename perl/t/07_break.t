use Test::More;
use Data::MessagePack;
use t::Util;
no warnings 'uninitialized'; # i need this. i need this.

plan tests => 1;

my $d = Data::MessagePack->unpack(Data::MessagePack->pack([{x => undef}]));
$d->[0]->{x} = 1;
ok delete $d->[0]->{x};
$d->[0] = 4;

