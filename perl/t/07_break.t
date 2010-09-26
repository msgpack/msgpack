use Test::More;
use Data::MessagePack;
use t::Util;

plan tests => 4;

my $d = Data::MessagePack->unpack(Data::MessagePack->pack({
    nil   => undef,
    true  => true,
    false => false,
    foo   => [undef, true, false],
}));

$d->{nil} = 42;
is $d->{nil}, 42;

$d->{true} = 43;
is $d->{true}, 43;

$d->{false} = 44;
is $d->{false}, 44;

is_deeply $d->{foo}, [undef, true, false];
