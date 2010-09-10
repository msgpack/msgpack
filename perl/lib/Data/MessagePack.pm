package Data::MessagePack;
use strict;
use warnings;
use 5.008001;

our $VERSION = '0.21';
our $PreferInteger = 0;

our $true  = do { bless \(my $dummy = 1), "Data::MessagePack::Boolean" };
our $false = do { bless \(my $dummy = 0), "Data::MessagePack::Boolean" };
sub true  () { $true  }
sub false () { $false }

if ( !__PACKAGE__->can('pack') ) { # this idea comes from Text::Xslate
    my $backend = $ENV{ PERL_DATA_MESSAGEPACK } || '';
    if ( $backend !~ /\b pp \b/xms ) {
        eval {
            require XSLoader;
            XSLoader::load(__PACKAGE__, $VERSION);
        };
        die $@ if $@ && $backend =~ /\b xs \b/xms; # force XS
    }
    if ( !__PACKAGE__->can('pack') ) {
        require 'Data/MessagePack/PP.pm';
    }
}

1;
__END__

=head1 NAME

Data::MessagePack - MessagePack serialising/deserialising

=head1 SYNOPSIS

    my $packed = Data::MessagePack->pack($dat);
    my $unpacked = Data::MessagePack->unpack($dat);

=head1 DESCRIPTION

This module converts Perl data structures to MessagePack and vice versa.

=head1 ABOUT MESSAGEPACK FORMAT

MessagePack is a binary-based efficient object serialization format.
It enables to exchange structured objects between many languages like JSON. But unlike JSON, it is very fast and small.

=head2 ADVANTAGES

=over 4

=item PORTABILITY

Messagepack is language independent binary serialize format.

=item SMALL SIZE

    say length(JSON::XS::encode_json({a=>1, b=>2}));   # => 13
    say length(Storable::nfreeze({a=>1, b=>2}));       # => 21
    say length(Data::MessagePack->pack({a=>1, b=>2})); # => 7

MessagePack format saves memory than JSON and Storable format.

=item STREAMING DESERIALIZER

MessagePack supports streaming deserializer. It is useful for networking such as RPC.

=back

If you want to get more informations about messagepack format, please visit to L<http://msgpack.org/>.

=head1 METHODS

=over 4

=item my $packed = Data::MessagePack->pack($data[, $max_depth]);

Pack the $data to messagepack format string.

This method throws exception when nesting perl structure more than $max_depth(default: 512) for detecting circular reference.

Data::MessagePack->pack() throws exception when encountered blessed object. Because MessagePack is language independent format.

=item my $unpacked = Data::MessagePack->unpack($msgpackstr);

unpack the $msgpackstr to messagepack format string.

=back

=head1 Configuration Variables

=over 4

=item $Data::MessagePack::PreferInteger

Pack the string as int when the value looks like int(EXPERIMENTAL).

=back

=head1 SPEED

This is result of benchmark/serialize.pl and benchmark/deserialize.pl on my SC440(Linux 2.6.32-23-server #37-Ubuntu SMP).

    -- serialize
    JSON::XS: 2.3
    Data::MessagePack: 0.20
    Storable: 2.21
    Benchmark: timing 1000000 iterations of json, mp, storable...
          json:  5 wallclock secs ( 3.95 usr +  0.00 sys =  3.95 CPU) @ 253164.56/s (n=1000000)
            mp:  3 wallclock secs ( 2.69 usr +  0.00 sys =  2.69 CPU) @ 371747.21/s (n=1000000)
      storable: 26 wallclock secs (27.21 usr +  0.00 sys = 27.21 CPU) @ 36751.19/s (n=1000000)

    -- deserialize
    JSON::XS: 2.3
    Data::MessagePack: 0.20
    Storable: 2.21
    Benchmark: timing 1000000 iterations of json, mp, storable...
          json:  4 wallclock secs ( 4.45 usr +  0.00 sys =  4.45 CPU) @ 224719.10/s (n=1000000)
            mp:  6 wallclock secs ( 5.45 usr +  0.00 sys =  5.45 CPU) @ 183486.24/s (n=1000000)
      storable:  7 wallclock secs ( 7.77 usr +  0.00 sys =  7.77 CPU) @ 128700.13/s (n=1000000)

=head1 AUTHORS

Tokuhiro Matsuno

Makamaka Hannyaharamitu

=head1 THANKS TO

Jun Kuriyama

Dan Kogai

FURUHASHI Sadayuki

=head1 LICENSE

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.


=head1 SEE ALSO

L<http://msgpack.org/> is official web site for MessagePack format.

