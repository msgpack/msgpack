package t::Util;
use strict;
use warnings;
use Data::MessagePack;

sub import {
    my $pkg = caller(0);

    strict->import;
    warnings->import;

    no strict 'refs';
    *{"$pkg\::true"} = sub () {
        Data::MessagePack::true()
    };
    *{"$pkg\::false"} = sub () {
        Data::MessagePack::false()
    };
    *{"$pkg\::null"} = sub() { undef };
}

1;
