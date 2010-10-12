use strict;
use warnings;
use Data::MessagePack;
use Test::More;
use t::Util;

my @input = (
    [[]],
    [[],[]],
    [{"a" => 97},{"a" => 97}],
    [{"a" => 97},{"a" => 97},{"a" => 97}],
    [ map { +{ "foo $_" => "bar $_" } } 'aa' .. 'zz' ],
    [42, null],
    [42, true],
    [42, false],
);

plan tests => @input * 2;

for my $input (@input) {
    my $packed = Data::MessagePack->pack($input);
    my $up = Data::MessagePack::Unpacker->new();
    $up->execute($packed, 0);
    ok $up->is_finished, 'finished';
    is_deeply($up->data, $input);
}

