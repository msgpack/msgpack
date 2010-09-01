package Data::MessagePack::PP;

use 5.008000;
use strict;
use B ();
use Scalar::Util qw( blessed );
use Carp ();

our $VERSION = '0.03';


# copied from Data::MessagePack
our $true  = do { bless \(my $dummy = 1), "Data::MessagePack::Boolean" };
our $false = do { bless \(my $dummy = 0), "Data::MessagePack::Boolean" };

sub true  () { $true  }
sub false () { $false }

our $PreferInteger;

# See also
# http://redmine.msgpack.org/projects/msgpack/wiki/FormatSpec
# http://cpansearch.perl.org/src/YAPPO/Data-Model-0.00006/lib/Data/Model/Driver/Memcached.pm
# http://frox25.no-ip.org/~mtve/wiki/MessagePack.html : reference to using CORE::pack, CORE::unpack


BEGIN {
    # for pack and unpack compatibility
    if ( $] < 5.010 ) {
        require Data::Float;
        *pack_double = sub {
            my $float_hex = Data::Float::float_hex( $_[0] );
            my ( $sign, $sgnf, $exp ) = $float_hex =~ /^([-+])0x1\.([a-z0-9]+)p([-+][\d]+)$/;
            my @bits;

            $sign = $sign eq '-' ? 1 : 0;
            $exp  = sprintf( '%011b', 1023 + $exp );

            my $bit  = $sign . $exp . join( '', map { unpack('B4', pack('H', $_) ) } split //, $sgnf );

            while ( $bit =~ /(.{8})/g ) {
                push @bits, $1;
            }

             return pack( 'C*', 0xcb, map { unpack( 'C', pack("B*", $_ ) ) } @bits );
        };
        *unpack_double = sub {
            my $bits = join('', map { sprintf('%08b', $_) } unpack( 'C*', substr( $_[0], $_[1], 8 ) ) );
            my $sign = substr($bits, 0, 1) ? '-' : '+';
            my $sgnf = substr($bits, 12, 52);
            my $exp  = substr($bits, 1, 11);
            $bits = '';
            while ( $sgnf =~ /(.{4})/g ) {
                $bits .= unpack('H',pack('B4', $1));
            }
            $exp = ((unpack("C*",(pack("B8", (substr('00000'.$exp,0,8) )))) <<8 )
                    + unpack("C*",(pack("B8", (substr('00000'.$exp,8,8) ))))) - 1023;
            return Data::Float::hex_float( $sign . '0x1.' . $bits . 'p' . $exp ) + 0.0;
        };
        *unpack_float  = sub { Carp::croak("unpack_float is disable in less than Perl 5.10"); };
        *unpack_int16  = sub {
            my $v = unpack 'n', substr( $_[0], $_[1], 2 );
            return $v ? $v - 0x10000 : 0;
        };
        *unpack_int32  = sub {
            my $v = unpack 'N', substr( $_[0], $_[1], 4 );
            return $v ? -(~$v + 1) : $v;
        };
        *unpack_int64  = sub { Carp::croak("unpack_int64 is disable in less than Perl 5.10"); };
    }
    else {
        *pack_double   = sub { return pack 'Cd>', 0xcb, $_[0]; };
        *unpack_double = sub { return unpack( 'd>', substr( $_[0], $_[1], 8 ) ); };
        *unpack_float  = sub { return unpack( 'f>', substr( $_[0], $_[1], 4 ) ); };
        *unpack_int16  = sub { return unpack 'n!',  substr( $_[0], $_[1], 2 ); };
        *unpack_int32  = sub { return unpack 'N!',  substr( $_[0], $_[1], 4 ); };
        *unpack_int64  = sub { return unpack 'Q>',  substr( $_[0], $_[1], 8 ); };
    }
    # for 5.8 etc.
    unless ( defined &utf8::is_utf8 ) {
       require Encode;
       *utf8::is_utf8 = *Encode::is_utf8;
    }
}


#
# PACK
#

{
    my $max_depth;

sub pack {
    Carp::croak('Usage: Data::MessagePack->pack($dat [,$max_depth])') if @_ < 2;
    $max_depth = defined $_[2] ? $_[2] : 512; # init
    return _pack( $_[1] );
}


sub _pack {
    my ( $value ) = @_;

    return pack( 'C', 0xc0 ) if ( not defined $value );

    my $b_obj = B::svref_2object( ref $value ? $value : \$value );

    if ( $b_obj->isa('B::AV') ) {
        my $num = @$value;
        my $header = 
              $num < 16          ? pack( 'C',  0x90 + $num )
            : $num < 2 ** 16 - 1 ? pack( 'Cn', 0xdc,  $num )
            : $num < 2 ** 32 - 1 ? pack( 'CN', 0xdd,  $num )
            : die "" # don't arrivie here
        ;
        if ( --$max_depth <= 0 ) {
            Carp::croak("perl structure exceeds maximum nesting level (max_depth set too low?)");
        }
        return join( '', $header, map { _pack( $_ ) } @$value );
    }

    elsif ( $b_obj->isa('B::HV') ) {
        my $num = keys %$value;
        my $header = 
              $num < 16          ? pack( 'C',  0x80 + $num )
            : $num < 2 ** 16 - 1 ? pack( 'Cn', 0xde,  $num )
            : $num < 2 ** 32 - 1 ? pack( 'CN', 0xdf,  $num )
            : die "" # don't arrivie here
        ;
        if ( --$max_depth <= 0 ) {
            Carp::croak("perl structure exceeds maximum nesting level (max_depth set too low?)");
        }
        return join( '', $header, map { _pack( $_ ) } %$value );
    }

    elsif ( blessed( $value ) eq 'Data::MessagePack::Boolean' ) {
        return  pack( 'C', $$value ? 0xc3 : 0xc2 );
    }

    my $flags = $b_obj->FLAGS;

    if ( $flags & ( B::SVf_IOK | B::SVp_IOK ) ) {

        if ($value >= 0) {
            return    $value <= 127 ?    pack 'C',        $value
                    : $value < 2 ** 8 ?  pack 'CC', 0xcc, $value
                    : $value < 2 ** 16 ? pack 'Cn', 0xcd, $value
                    : $value < 2 ** 32 ? pack 'CN', 0xce, $value
                    : pack 'CQ>', 0xcf, $value;
        }
        else {
            return    -$value <= 32 ?      pack 'C',        $value
                    : -$value <= 2 **  7 ? pack 'Cc', 0xd0, $value
                    : -$value <= 2 ** 15 ? pack 'Cn', 0xd1, $value
                    : -$value <= 2 ** 31 ? pack 'CN', 0xd2, $value
                    : pack 'Cq>', 0xd3, $value;
        }

    }

    elsif ( $flags & B::SVf_POK ) { # raw / check needs before dboule

        if ( $PreferInteger ) {
            if ( $value =~ /^-?[0-9]+$/ ) { # ok?
                my $value2 = 0 + $value;
                if (  0 + $value != B::svref_2object( \$value2 )->int_value ) {
                    local $PreferInteger;      # avoid for PV => NV
                    return _pack( "$value" );
                }
                return _pack( $value + 0 );
            }
        }

        utf8::encode( $value ) if utf8::is_utf8( $value );

        my $num = length $value;
        my $header = 
              $num < 32          ? pack( 'C',  0xa0 + $num )
            : $num < 2 ** 16 - 1 ? pack( 'Cn', 0xda, $num )
            : $num < 2 ** 32 - 1 ? pack( 'CN', 0xdb, $num )
            : die "" # don't arrivie here
        ;

        return $header . $value;

    }

    elsif ( $flags & ( B::SVf_NOK | B::SVp_NOK ) ) { # double only
        return pack_double( $value );
    }

    else {
        die "???";
    }

}

} # PACK


#
# UNPACK
#

{
    my $p; # position variables for speed.

sub unpack {
    $p = 0; # init
    _unpack( $_[1] );
}


sub _unpack {
    my ( $value ) = @_;
    my $byte = unpack( 'C', substr( $value, $p++, 1 ) ); # get header

    die "invalid data" unless defined $byte;

    if ( ( $byte >= 0x90 and $byte <= 0x9f ) or $byte == 0xdc or $byte == 0xdd ) {
        my $num;
        if ( $byte == 0xdc ) { # array 16
            $num = unpack 'n', substr( $value, $p, 2 );
            $p += 2;
        }
        elsif ( $byte == 0xdd ) { # array 32
            $num = unpack 'N', substr( $value, $p, 4 );
            $p += 4;
        }
        else { # fix array
            $num = $byte & ~0x90;
        }
        my @array;
        push @array, _unpack( $value ) while $num-- > 0;
        return \@array;
    }

    elsif ( ( $byte >= 0x80 and $byte <= 0x8f ) or $byte == 0xde or $byte == 0xdf ) {
        my $num;
        if ( $byte == 0xde ) { # map 16
            $num = unpack 'n', substr( $value, $p, 2 );
            $p += 2;
        }
        elsif ( $byte == 0xdf ) { # map 32
            $num = unpack 'N', substr( $value, $p, 4 );
            $p += 4;
        }
        else { # fix map
            $num = $byte & ~0x80;
        }
        my %map;
        for ( 0 .. $num - 1 ) {
            my $key = _unpack( $value );
            my $val = _unpack( $value );
            $map{ $key } = $val;
        }
        return \%map;
    }

    elsif ( $byte >= 0x00 and $byte <= 0x7f ) { # positive fixnum
        return $byte;
    }
    elsif ( $byte == 0xcc ) { # uint8
        unpack( 'C', substr( $value, $p++, 1 ) );
    }
    elsif ( $byte == 0xcd ) { # uint16
        $p += 2;
        return unpack 'n', substr( $value, $p - 2, 2 );
    }
    elsif ( $byte == 0xce ) { # unit32
        $p += 4;
        return unpack 'N', substr( $value, $p - 4, 4 );
    }
    elsif ( $byte == 0xcf ) { # unit64
        $p += 8;
        return unpack 'Q>', substr( $value, $p - 8, 8 );
    }
    elsif ( $byte == 0xd3 ) { # int64
        $p += 8;
        return unpack_int64( $value, $p - 8 );
        return unpack 'q>',  substr( $value, $p - 8, 8 );
    }
    elsif ( $byte == 0xd2 ) { # int32
        $p += 4;
        return unpack_int32( $value, $p - 4 );
    }
    elsif ( $byte == 0xd1 ) { # int16
        $p += 2;
        return unpack_int16( $value, $p - 2 );
    }
    elsif ( $byte == 0xd0 ) { # int8
        return unpack 'c',  substr( $value, $p++, 1 ); # c / C
    }
    elsif ( $byte >= 0xe0 and $byte <= 0xff ) { # negative fixnum
        return $byte - 256;
    }

    elsif ( ( $byte >= 0xa0 and $byte <= 0xbf ) or $byte == 0xda or $byte == 0xdb ) { # raw
        my $num;
        if ( $byte == 0xda ) {
            $num = unpack 'n', substr( $value, $p, 2 );
            $p += 2 + $num;
        }
        elsif ( $byte == 0xdb ) {
            $num = unpack 'N', substr( $value, $p, 4 );
            $p += 4 + $num;
        }
        else { # fix raw
            $num = $byte & ~0xa0;
            $p += $num;
        }
        return substr( $value, $p - $num, $num );
    }

    elsif ( $byte == 0xc0 ) { # nil
        return undef;
    }
    elsif ( $byte == 0xc2 ) { # boolean
        return false;
    }
    elsif ( $byte == 0xc3 ) { # boolean
        return true;
    }

    elsif ( $byte == 0xcb ) { # double
        $p += 8;
        return unpack_double( $value, $p - 8 );
    }

    elsif ( $byte == 0xca ) { # float
        $p += 4;
        return unpack_float( $value, $p - 4 );
    }

    else {
        die "???";
    }

}


} # UNPACK


#
# Data::MessagePack::Unpacker
#

package Data::MessagePack::PP::Unpacker;

use strict;

sub new {
    bless { stack => [] }, shift;
}


sub execute_limit {
    execute( @_ );
}


{
    my $p;
    #my $r; # remained data.

sub execute {
    my ( $self, $data, $offset, $limit ) = @_;
    #my $value = ( defined $self->{ remain } ? $self->{ remain } : '' ) . substr( $data, $offset, $limit );
    my $value = substr( $data, $offset, $limit ? $limit : length $data );
    my $len   = length $value;

    $p = 0;
    #$r = 0;

    while ( $len > $p ) {
        _count( $self, $value ) or last;

        if ( @{ $self->{stack} } > 0 ) {
            $self->{stack}->[-1];
            pop @{ $self->{stack} } if --$self->{stack}->[-1] == 0;
        }
    }

    if ( $len == $p ) {
        $self->{ data } .= substr( $value, 0, $p );
        $self->{ remain } = undef;
    }
    else { # I thought this feature is needed. but XS version can't do so
        #$self->{ remain } = substr( $value, 0, $p + $r );
    }

    return $p;
}


sub _count {
    my ( $self, $value ) = @_;
    my $byte = unpack( 'C', substr( $value, $p++, 1 ) ); # get header

    if ( ( $byte >= 0x90 and $byte <= 0x9f ) or $byte == 0xdc or $byte == 0xdd ) {
        my $num;
        if ( $byte == 0xdc ) { # array 16
            # I thought this feature is needed. but XS version can't do so. So commented out.
            #my $len = length substr( $value, $p, 2 );
            #if ( $len != 2 ) {
            #    $r = $len;
            #    return 0;
            #}
            $num = unpack 'n', substr( $value, $p, 2 );
            $p += 2;
        }
        elsif ( $byte == 0xdd ) { # array 32
            $num = unpack 'N', substr( $value, $p, 4 );
            $p += 4;
        }
        else { # fix array
            $num = $byte & ~0x90;
        }

        push @{ $self->{stack} }, $num + 1;

        return 1;
    }

    elsif ( ( $byte >= 0x80 and $byte <= 0x8f ) or $byte == 0xde or $byte == 0xdf ) {
        my $num;
        if ( $byte == 0xde ) { # map 16
            $num = unpack 'n', substr( $value, $p, 2 );
            $p += 2;
        }
        elsif ( $byte == 0xdf ) { # map 32
            $num = unpack 'N', substr( $value, $p, 4 );
            $p += 4;
        }
        else { # fix map
            $num = $byte & ~0x80;
        }

        push @{ $self->{stack} }, $num * 2 + 1; # a pair

        return 1;
    }

    elsif ( $byte == 0xc0 or $byte == 0xc2 or $byte == 0xc3 ) { # nil, false, true
        return 1;
    }

    elsif ( $byte >= 0x00 and $byte <= 0x7f ) { # positive fixnum
        return 1;
    }

    elsif ( $byte >= 0xcc and $byte <= 0xcf ) { # uint
        $p += $byte == 0xcc ? 1
            : $byte == 0xcd ? 2
            : $byte == 0xce ? 4
            : $byte == 0xcf ? 8
            : die;
        return 1;
    }

    elsif ( $byte >= 0xd0 and $byte <= 0xd3 ) { # int
        $p += $byte == 0xd0 ? 1
            : $byte == 0xd1 ? 2
            : $byte == 0xd2 ? 4
            : $byte == 0xd3 ? 8
            : die;
        return 1;
    }

    elsif ( $byte >= 0xe0 and $byte <= 0xff ) { # negative fixnum
        return 1;
    }

    elsif ( $byte >= 0xca and $byte <= 0xcb ) { # float, double
        $p += $byte == 0xca ? 4 : 8;
        return 1;
    }

    elsif ( ( $byte >= 0xa0 and $byte <= 0xbf ) or $byte == 0xda or $byte == 0xdb ) {
        my $num;
        if ( $byte == 0xda ) {
            $num = unpack 'n', substr( $value, $p, 2 );
            $p += 2;
        }
        elsif ( $byte == 0xdb ) {
            $num = unpack 'N', substr( $value, $p, 4 );
            $p += 4;
        }
        else { # fix raw
            $num = $byte & ~0xa0;
        }
        $p += $num;
        return 1;
    }

    else {
        die "???";
    }

    return 0;
}

} # execute


sub data {
    my $data = Data::MessagePack->unpack( $_[0]->{ data } );
    $_[0]->reset;
    return $data;
}


sub is_finished {
    my ( $self ) = @_;
    ( scalar( @{ $self->{stack} } ) or defined $self->{ remain } ) ? 0 : 1;
}


sub reset {
    $_[0]->{ stack }  = [];
    $_[0]->{ data }   = undef;
    $_[0]->{ remain } = undef;
}

1;
__END__

=pod

=head1 NAME

Data::MessagePack::PP - the pure perl version of Data::MessagePack

=head1 LIMITATION

Currently this module works completely in Perl 5.10 or later.
In Perl 5.8.x, it requires L<Data::Float> and cannot unpack int64 and float (pack int64 too).


=head1 SEE ALSO

L<Data::MessagePack>,
L<http://frox25.no-ip.org/~mtve/wiki/MessagePack.html>,
L<Data::Float>

=head1 AUTHOR

makamaka

=head1 COPYRIGHT AND LICENSE

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself. 

=cut
