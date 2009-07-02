use t::Util;
use Test::More;
use Data::MessagePack;
use Data::Dumper;
no warnings; # shut up "Integer overflow in hexadecimal number"

sub packit {
    local $_ = unpack("H*", Data::MessagePack->pack($_[0]));
    s/(..)/$1 /g;
    s/ $//;
    $_;
}

sub pis ($$) {
    is packit($_[0]), $_[1], 'dump ' . $_[1];
    # is(Dumper(Data::MessagePack->unpack(Data::MessagePack->pack($_[0]))), Dumper($_[0]));
}

my @dat = (
    '0',     '00',
    '1',     '01',
    '10',     '0a',
    ''.0xEFFF => 'cd ef ff',
    ''.0xFFFF => 'cd ff ff',
    ''.0xFFFFFF => 'ce 00 ff ff ff',
    ''.0xFFFFFFFF => 'aa 34 32 39 34 39 36 37 32 39 35',
    ''.0xFFFFFFFFF => 'ab 36 38 37 31 39 34 37 36 37 33 35',
    ''.0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFF => 'b4 38 2e 33 30 37 36 37 34 39 37 33 36 35 35 37 32 65 2b 33 34',
    {'0' => '1'}, '81 00 01',
    {'abc' => '1'}, '81 a3 61 62 63 01',
);
plan tests => 1*(scalar(@dat)/2);

$Data::MessagePack::PreferInteger = 1;
for (my $i=0; $i<scalar(@dat); ) {
    pis $dat[$i++], $dat[$i++];
}

