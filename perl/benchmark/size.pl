#!/usr/bin/perl
use strict;
use warnings;
use Data::MessagePack;
use Storable;
use Text::SimpleTable;

my @entries = (
    '1',
    '3.14',
    '{}',
    '[]',
    "[('a')x10]",
    "{('a')x10}",
    "+{1,+{1,+{}}}",
    "+[+[+[]]]",
);

my $table = Text::SimpleTable->new([15, 'src'], [9, 'storable'], [7, 'msgpack']);

for my $src (@entries) {
    my $e = eval $src;
    die $@ if $@;

    $table->row(
        $src,
        length(Storable::nfreeze(ref $e ? $e : \$e)),
        length(Data::MessagePack->pack($e)),
    );
}

print "perl: $]\n";
print "Storable: $Storable::VERSION\n";
print "Data::MessagePack: $Data::MessagePack::VERSION\n";
print "\n";
print $table->draw;

