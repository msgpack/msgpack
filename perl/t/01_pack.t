use t::Util;
use Test::More;
use Data::MessagePack;

sub packit {
    local $_ = unpack("H*", Data::MessagePack->pack($_[0]));
    s/(..)/$1 /g;
    s/ $//;
    $_;
}

sub pis ($$) {
    is packit($_[0]), $_[1], 'dump ' . $_[1];
}

my @dat = (
    0,     '00',
    (my $foo="0")+0, '00',
    {2 => undef}, '81 a1 32 c0',
    do {no warnings; my $foo = 10; "$foo"; $foo = undef; $foo} => 'c0', # PVIV but !POK && !IOK
    1,     '01',
    127,   '7f',
    128,   'cc 80',
    255,   'cc ff',
    256,   'cd 01 00',
    65535, 'cd ff ff',
    65536, 'ce 00 01 00 00',
    -1,    'ff',
    -32,   'e0',
    -33,   'd0 df',
    -128,  'd0 80',
    -129,  'd1 ff 7f',
    -32768, 'd1 80 00',
    -32769, 'd2 ff ff 7f ff',
    1.0,   'cb 3f f0 00 00 00 00 00 00',
    do { my $x=3.0;my $y = "$x";$x },   'a1 33', # PVNV
    "",    'a0',
    "a",   'a1 61',
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 'bf 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61',
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 'da 00 20 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61 61',
    undef, 'c0',
    Data::MessagePack::true(), 'c3',
    Data::MessagePack::false(), 'c2',
    [], '90',
    [+[]], '91 90',
    [[], undef], '92 90 c0',
    {'a', 0}, '81 a1 61 00',
    8388608, 'ce 00 80 00 00',

    [undef, false, true], '93 c0 c2 c3',
    ["", "a", "bc", "def"], '94 a0 a1 61 a2 62 63 a3 64 65 66',
    [[], [[undef]]], '92 90 91 91 c0',
    [undef, false, true], '93 c0 c2 c3',
    [[0, 64, 127], [-32, -16, -1]], '92 93 00 40 7f 93 e0 f0 ff',
    [0, -128, -1, 0, -32768, -1, 0, -2147483648, -1], '99 00 d0 80 ff 00 d1 80 00 ff 00 d2 80 00 00 00 ff',
    2147483648, 'ce 80 00 00 00',
    -2147483648, 'd2 80 00 00 00',
    'a' x 0x0100, 'da 01 00' . (' 61' x 0x0100),
    [(undef) x 0x0100], 'dc 01 00' . (' c0' x 0x0100),
);
plan tests => 1*(scalar(@dat)/2);

for (my $i=0; $i<scalar(@dat); ) {
    pis $dat[$i++], $dat[$i++];
}

