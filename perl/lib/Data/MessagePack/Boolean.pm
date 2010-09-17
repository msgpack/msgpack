package Data::MessagePack::Boolean;
use strict;
use overload
    'bool' => sub { ${ $_[0] } },
    '0+'   => sub { ${ $_[0] } },
    '""'   => sub { ${ $_[0] } ? 'true' : 'false' },

    fallback => 1,
;

our $true  = do { bless \(my $dummy = 1) };
our $false = do { bless \(my $dummy = 0) };

1;
