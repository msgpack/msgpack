package t::Util;
use strict;
use warnings;

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
}

1;
