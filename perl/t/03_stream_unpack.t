use t::Util;
use Test::More;
use Data::MessagePack;

no warnings 'uninitialized'; # i need this. i need this.

my $up = Data::MessagePack::Unpacker->new;
sub unpackit {
    my $v = $_[0];
    $v =~ s/ //g;
    $v = pack 'H*', $v;
    $up->reset;
    my $ret = $up->execute($v, 0);
    if ($ret != length($v)) {
        fail "extra bytes";
    }
    return $up->data;
}

sub pis ($$) {
    is_deeply unpackit($_[0]), $_[1], 'dump ' . $_[0];
}

my @dat = do 't/data.pl';

plan tests => 1*(scalar(@dat)/2) + 3;

isa_ok $up, 'Data::MessagePack::Unpacker';
for (my $i=0; $i<scalar(@dat); ) {
    pis $dat[$i++], $dat[$i++];
}

# devided.
{
    my $up = Data::MessagePack::Unpacker->new();
    $up->execute("\x95", 0); # array marker
    for (1..5) {
        $up->execute("\xc0", 0); # nil
    }
    ok $up->is_finished, 'finished';
    is_deeply $up->data, [undef, undef, undef, undef, undef], 'array, is_deeply';
}

