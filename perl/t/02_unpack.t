use Test::More;
use Data::MessagePack;
use t::Util;
no warnings 'uninitialized'; # i need this. i need this.

sub unpackit {
    my $v = $_[0];
    $v =~ s/ //g;
    $v = pack 'H*', $v;
    return Data::MessagePack->unpack($v);
}

sub pis ($$) {
    is_deeply unpackit($_[0]), $_[1], 'dump ' . $_[0];
}

my @dat = do 't/data.pl';

plan tests => 1*(scalar(@dat)/2);

for (my $i=0; $i<scalar(@dat); ) {
    pis $dat[$i++], $dat[$i++];
}

