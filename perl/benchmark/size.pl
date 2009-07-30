#!/usr/bin/perl
use strict;
use warnings;
use Data::MessagePack;
use Storable;
use Text::SimpleTable;

my @entries = (
    1,
    3.14,
    {},
    [],
    [('a')x10],
    {('a')x10},
    +{1,+{1,+{}}},
    +[+[+[]]],
);

my $table = Text::SimpleTable->new([10, 'storable'], [10, 'msgpack']);

for my $e (@entries) {
    $table->row(
        length(Storable::nfreeze(ref $e ? $e : \$e)),
        length(Data::MessagePack->pack($e)),
    );
}

print $table->draw;
