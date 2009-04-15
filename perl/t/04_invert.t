use Test::More;
use Data::MessagePack;
use t::Util;
no warnings 'uninitialized'; # i need this. i need this.

sub invert {
    return Data::MessagePack->unpack(
        Data::MessagePack->pack($_[0]),
    );
}

sub pis ($) {
    is_deeply invert($_[0]), $_[0], 'dump ' . $_[0];
}

my @dat = do 't/data.pl';

plan tests => 1*(scalar(@dat)/2);

for (my $i=0; $i<scalar(@dat); ) {
    $i++;
    pis $dat[$i++];
}

