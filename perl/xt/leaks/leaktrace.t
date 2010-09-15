#!perl -w
use strict;
use Test::Requires 'Test::LeakTrace';
use Test::More;

use Data::MessagePack;

my $data = {
    a => 'foo',
    b => 42,
    c => undef,
    d => [qw(bar baz)],
    e => 3.14,
};

no_leaks_ok {
    my $s = Data::MessagePack->pack($data);
};

no_leaks_ok {
    eval { Data::MessagePack->pack([\*STDIN]) };
    #note $@;
    $@ or die "it must die";
};

my $s = Data::MessagePack->pack($data);

no_leaks_ok {
    my $data = Data::MessagePack->unpack($s);
};

no_leaks_ok {
    my $ss = $s;
    chop $ss;
    eval { Data::MessagePack->unpack($ss) };
    #note $@;
    $@ or die "it must die";
};

done_testing;
