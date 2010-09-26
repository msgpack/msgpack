#!perl -w
use strict;
use Test::Requires { 'Test::LeakTrace' => 0.13 };
use Test::More;
use Data::MessagePack;
BEGIN {
    if($INC{'Data/MessagePack/PP.pm'}) {
        plan skip_all => 'disabled in PP';
     }
}

my $simple_data  = "xyz";
my $complex_data = {
    a => 'foo',
    b => 42,
    c => undef,
    d => [qw(bar baz)],
    e => 3.14,
};

note 'pack';

no_leaks_ok {
    my $s = Data::MessagePack->pack($complex_data);
};

no_leaks_ok {
    eval { Data::MessagePack->pack([\*STDIN]) };
    note $@;
    $@ or warn "# it must die";
};

note 'unpack';

my $s = Data::MessagePack->pack($simple_data);
my $c = Data::MessagePack->pack($complex_data);

no_leaks_ok {
    my $data = Data::MessagePack->unpack($s);
};

no_leaks_ok {
    my $data = Data::MessagePack->unpack($c);
};

no_leaks_ok {
    my $broken = $s;
    chop $broken;
    eval { Data::MessagePack->unpack($broken) };
    note $@;
    $@ or warn "# it must die";
};

note 'stream';

no_leaks_ok {
    my $up = Data::MessagePack::Unpacker->new();
    $up->execute($c);
    my $data = $up->data();
};

done_testing;
