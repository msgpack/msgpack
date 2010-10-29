package Data::MessagePack::PP;
use 5.008001;
use strict;
use warnings;
no warnings 'recursion';

use Carp ();
use B ();

# See also
# http://redmine.msgpack.org/projects/msgpack/wiki/FormatSpec
# http://cpansearch.perl.org/src/YAPPO/Data-Model-0.00006/lib/Data/Model/Driver/Memcached.pm
# http://frox25.no-ip.org/~mtve/wiki/MessagePack.html : reference to using CORE::pack, CORE::unpack

BEGIN {
    my $unpack_int64_slow;
    my $unpack_uint64_slow;

    if(!eval { pack 'Q', 1 }) { # don't have quad types
        # emulates quad types with Math::BigInt.
        # very slow but works well.
        $unpack_int64_slow = sub {
            require Math::BigInt;
            my $high = unpack_uint32( $_[0], $_[1] );
            my $low  = unpack_uint32( $_[0], $_[1] + 4);

            if($high < 0xF0000000) { # positive
                $high = Math::BigInt->new( $high );
                $low  = Math::BigInt->new( $low  );
                return +($high << 32 | $low)->bstr;
            }
            else { # negative
                $high = Math::BigInt->new( ~$high );
                $low  = Math::BigInt->new( ~$low  );
                return +( -($high << 32 | $low + 1) )->bstr;
            }
        };
        $unpack_uint64_slow = sub {
            require Math::BigInt;
            my $high = Math::BigInt->new( unpack_uint32( $_[0], $_[1]) );
            my $low  = Math::BigInt->new( unpack_uint32( $_[0], $_[1] + 4) );
            return +($high << 32 | $low)->bstr;
        };
    }

    *unpack_uint16 = sub { return unpack 'n', substr( $_[0], $_[1], 2 ) };
    *unpack_uint32 = sub { return unpack 'N', substr( $_[0], $_[1], 4 ) };

    # for pack and unpack compatibility
    if ( $] < 5.010 ) {
        # require $Config{byteorder}; my $bo_is_le = ( $Config{byteorder} =~ /^1234/ );
        # which better?
        my $bo_is_le = unpack ( 'd', "\x00\x00\x00\x00\x00\x00\xf0\x3f") == 1; # 1.0LE

        *unpack_int16  = sub {
            my $v = unpack 'n', substr( $_[0], $_[1], 2 );
            return $v ? $v - 0x10000 : 0;
        };
        *unpack_int32  = sub {
            no warnings; # avoid for warning about Hexadecimal number
            my $v = unpack 'N', substr( $_[0], $_[1], 4 );
            return $v ? $v - 0x100000000 : 0;
        };

        # In reality, since 5.9.2 '>' is introduced. but 'n!' and 'N!'?
        if($bo_is_le) {
            *pack_uint64 = sub {
                my @v = unpack( 'V2', pack( 'Q', $_[0] ) );
                return pack 'CN2', 0xcf, @v[1,0];
            };
            *pack_int64 = sub {
                my @v = unpack( 'V2', pack( 'q', $_[0] ) );
                return pack 'CN2', 0xd3, @v[1,0];
            };
            *pack_double = sub {
                my @v = unpack( 'V2', pack( 'd', $_[0] ) );
                return pack 'CN2', 0xcb, @v[1,0];
            };

            *unpack_float = sub {
                my @v = unpack( 'v2', substr( $_[0], $_[1], 4 ) );
                return unpack( 'f', pack( 'n2', @v[1,0] ) );
            };
            *unpack_double = sub {
                my @v = unpack( 'V2', substr( $_[0], $_[1], 8 ) );
                return unpack( 'd', pack( 'N2', @v[1,0] ) );
            };

            *unpack_int64 = $unpack_int64_slow || sub {
                my @v = unpack( 'V*', substr( $_[0], $_[1], 8 ) );
                return unpack( 'q', pack( 'N2', @v[1,0] ) );
            };
            *unpack_uint64 = $unpack_uint64_slow || sub {
                my @v = unpack( 'V*', substr( $_[0], $_[1], 8 ) );
                return unpack( 'Q', pack( 'N2', @v[1,0] ) );
            };
        }
        else { # big endian
            *pack_uint64   = sub { return pack 'CQ', 0xcf, $_[0]; };
            *pack_int64    = sub { return pack 'Cq', 0xd3, $_[0]; };
            *pack_double   = sub { return pack 'Cd', 0xcb, $_[0]; };

            *unpack_float  = sub { return unpack( 'f', substr( $_[0], $_[1], 4 ) ); };
            *unpack_double = sub { return unpack( 'd', substr( $_[0], $_[1], 8 ) ); };
            *unpack_int64  = $unpack_int64_slow  || sub { unpack 'q', substr( $_[0], $_[1], 8 ); };
            *unpack_uint64 = $unpack_uint64_slow || sub { unpack 'Q', substr( $_[0], $_[1], 8 ); };
        }
    }
    else { # 5.10.0 or later
        # pack_int64/uint64 are used only when the perl support quad types
        *pack_uint64   = sub { return pack 'CQ>', 0xcf, $_[0]; };
        *pack_int64    = sub { return pack 'Cq>', 0xd3, $_[0]; };
        *pack_double   = sub { return pack 'Cd>', 0xcb, $_[0]; };

        *unpack_float  = sub { return unpack( 'f>', substr( $_[0], $_[1], 4 ) ); };
        *unpack_double = sub { return unpack( 'd>', substr( $_[0], $_[1], 8 ) ); };
        *unpack_int16  = sub { return unpack( 'n!', substr( $_[0], $_[1], 2 ) ); };
        *unpack_int32  = sub { return unpack( 'N!', substr( $_[0], $_[1], 4 ) ); };

        *unpack_int64  = $unpack_int64_slow  || sub { return unpack( 'q>', substr( $_[0], $_[1], 8 ) ); };
        *unpack_uint64 = $unpack_uint64_slow || sub { return unpack( 'Q>', substr( $_[0], $_[1], 8 ) ); };
    }

    # fixin package symbols
    no warnings 'once';
    sub pack   :method;
    sub unpack :method;
    *Data::MessagePack::pack   = \&pack;
    *Data::MessagePack::unpack = \&unpack;

    @Data::MessagePack::Unpacker::ISA = qw(Data::MessagePack::PP::Unpacker);

    *true  = \&Data::MessagePack::true;
    *false = \&Data::MessagePack::false;
}

sub _unexpected {
    Carp::confess("Unexpected " . sprintf(shift, @_) . " found");
}

#
# PACK
#

our $_max_depth;

sub pack :method {
    Carp::croak('Usage: Data::MessagePack->pack($dat [,$max_depth])') if @_ < 2;
    $_max_depth = defined $_[2] ? $_[2] : 512; # init
    return _pack( $_[1] );
}


sub _pack {
    my ( $value ) = @_;

    local $_max_depth = $_max_depth - 1;

    if ( $_max_depth < 0 ) {
        Carp::croak("perl structure exceeds maximum nesting level (max_depth set too low?)");
    }

    return CORE::pack( 'C', 0xc0 ) if ( not defined $value );

    if ( ref($value) eq 'ARRAY' ) {
        my $num = @$value;
        my $header =
              $num < 16          ? CORE::pack( 'C',  0x90 + $num )
            : $num < 2 ** 16 - 1 ? CORE::pack( 'Cn', 0xdc,  $num )
            : $num < 2 ** 32 - 1 ? CORE::pack( 'CN', 0xdd,  $num )
            : _unexpected("number %d", $num)
        ;
        return join( '', $header, map { _pack( $_ ) } @$value );
    }

    elsif ( ref($value) eq 'HASH' ) {
        my $num = keys %$value;
        my $header =
              $num < 16          ? CORE::pack( 'C',  0x80 + $num )
            : $num < 2 ** 16 - 1 ? CORE::pack( 'Cn', 0xde,  $num )
            : $num < 2 ** 32 - 1 ? CORE::pack( 'CN', 0xdf,  $num )
            : _unexpected("number %d", $num)
        ;
        return join( '', $header, map { _pack( $_ ) } %$value );
    }

    elsif ( ref( $value ) eq 'Data::MessagePack::Boolean' ) {
        return  CORE::pack( 'C', ${$value} ? 0xc3 : 0xc2 );
    }


    my $b_obj = B::svref_2object( \$value );
    my $flags = $b_obj->FLAGS;

    if ( $flags & ( B::SVf_IOK | B::SVp_IOK ) ) {

        if ($value >= 0) {
            return    $value <= 127 ?    CORE::pack 'C',        $value
                    : $value < 2 ** 8 ?  CORE::pack 'CC', 0xcc, $value
                    : $value < 2 ** 16 ? CORE::pack 'Cn', 0xcd, $value
                    : $value < 2 ** 32 ? CORE::pack 'CN', 0xce, $value
                    : pack_uint64( $value );
        }
        else {
            return    -$value <= 32 ?      CORE::pack 'C', ($value & 255)
                    : -$value <= 2 **  7 ? CORE::pack 'Cc', 0xd0, $value
                    : -$value <= 2 ** 15 ? CORE::pack 'Cn', 0xd1, $value
                    : -$value <= 2 ** 31 ? CORE::pack 'CN', 0xd2, $value
                    : pack_int64( $value );
        }

    }
    elsif ( $flags & B::SVf_POK ) { # raw / check needs before dboule

        if ( $Data::MessagePack::PreferInteger ) {
            if ( $value =~ /^-?[0-9]+$/ ) { # ok?
                # checks whether $value is in (u)int32
                my $ivalue = 0 + $value;
                if (!(
                       $ivalue > 0xFFFFFFFF
                    or $ivalue < '-'.0x80000000 # for XS compat
                    or $ivalue != B::svref_2object(\$ivalue)->int_value
                )) {
                    return _pack( $ivalue );
                }
                # fallthrough
            }
            # fallthrough
        }

        utf8::encode( $value ) if utf8::is_utf8( $value );

        my $num = length $value;
        my $header =
              $num < 32          ? CORE::pack( 'C',  0xa0 + $num )
            : $num < 2 ** 16 - 1 ? CORE::pack( 'Cn', 0xda, $num )
            : $num < 2 ** 32 - 1 ? CORE::pack( 'CN', 0xdb, $num )
            : _unexpected('number %d', $num)
        ;

        return $header . $value;

    }
    elsif ( $flags & ( B::SVf_NOK | B::SVp_NOK ) ) { # double only
        return pack_double( $value );
    }
    else {
        _unexpected("data type %s", $b_obj);
    }

}

#
# UNPACK
#

our $_utf8 = 0;
my $p; # position variables for speed.

sub unpack :method {
    $p = 0; # init
    my $data = _unpack( $_[1] );
    if($p < length($_[1])) {
        Carp::croak("Data::MessagePack->unpack: extra bytes");
    }
    return $data;
}

my $T_RAW             = 0x01;
my $T_ARRAY           = 0x02;
my $T_MAP             = 0x04;
my $T_DIRECT          = 0x08; # direct mapping (e.g. 0xc0 <-> nil)

my @typemap = ( (0x00) x 256 );

$typemap[$_] |= $T_ARRAY for
    0x90 .. 0x9f, # fix array
    0xdc,         # array16
    0xdd,         # array32
;
$typemap[$_] |= $T_MAP for
    0x80 .. 0x8f, # fix map
    0xde,         # map16
    0xdf,         # map32
;
$typemap[$_] |= $T_RAW for
    0xa0 .. 0xbf, # fix raw
    0xda,         # raw16
    0xdb,         # raw32
;

my @byte2value;
foreach my $pair(
    [0xc3, true],
    [0xc2, false],
    [0xc0, undef],

    (map { [ $_, $_ ] }         0x00 .. 0x7f), # positive fixnum
    (map { [ $_, $_ - 0x100 ] } 0xe0 .. 0xff), # negative fixnum
) {
    $typemap[    $pair->[0] ] |= $T_DIRECT;
    $byte2value[ $pair->[0] ]  = $pair->[1];
}

sub _unpack {
    my ( $value ) = @_;
    $p < length($value)
        or Carp::confess("Data::MessagePack->unpack: insufficient bytes");
    # get a header byte
    my $byte = ord( substr $value, $p, 1 );
    $p++;

    # +/- fixnum, nil, true, false
    return $byte2value[$byte] if $typemap[$byte] & $T_DIRECT;

    if ( $typemap[$byte] & $T_RAW ) {
        my $num;
        if ( $byte == 0xda ) {
            $num = CORE::unpack 'n', substr( $value, $p, 2 );
            $p += 2 + $num;
        }
        elsif ( $byte == 0xdb ) {
            $num = CORE::unpack 'N', substr( $value, $p, 4 );
            $p += 4 + $num;
        }
        else { # fix raw
            $num = $byte & ~0xa0;
            $p += $num;
        }
        my $s = substr( $value, $p - $num, $num );
        utf8::decode($s) if $_utf8;
        return $s;
    }
    elsif ( $typemap[$byte] & $T_ARRAY ) {
        my $num;
        if ( $byte == 0xdc ) { # array 16
            $num = CORE::unpack 'n', substr( $value, $p, 2 );
            $p += 2;
        }
        elsif ( $byte == 0xdd ) { # array 32
            $num = CORE::unpack 'N', substr( $value, $p, 4 );
            $p += 4;
        }
        else { # fix array
            $num = $byte & ~0x90;
        }
        my @array;
        push @array, _unpack( $value ) while --$num >= 0;
        return \@array;
    }
    elsif ( $typemap[$byte] & $T_MAP ) {
        my $num;
        if ( $byte == 0xde ) { # map 16
            $num = CORE::unpack 'n', substr( $value, $p, 2 );
            $p += 2;
        }
        elsif ( $byte == 0xdf ) { # map 32
            $num = CORE::unpack 'N', substr( $value, $p, 4 );
            $p += 4;
        }
        else { # fix map
            $num = $byte & ~0x80;
        }
        my %map;
        while ( --$num >= 0 ) {
            no warnings; # for undef key case
            my $key = _unpack( $value );
            my $val = _unpack( $value );
            $map{ $key } = $val;
        }
        return \%map;
    }

    elsif ( $byte == 0xcc ) { # uint8
        return CORE::unpack( 'C', substr( $value, $p++, 1 ) );
    }
    elsif ( $byte == 0xcd ) { # uint16
        $p += 2;
        return unpack_uint16( $value, $p - 2 );
    }
    elsif ( $byte == 0xce ) { # unit32
        $p += 4;
        return unpack_uint32( $value, $p - 4 );
    }
    elsif ( $byte == 0xcf ) { # unit64
        $p += 8;
        return unpack_uint64( $value, $p - 8 );
    }
    elsif ( $byte == 0xd3 ) { # int64
        $p += 8;
        return unpack_int64( $value, $p - 8 );
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
        return CORE::unpack 'c',  substr( $value, $p++, 1 ); # c / C
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
        _unexpected("byte 0x%02x", $byte);
    }
}


#
# Data::MessagePack::Unpacker
#

package
    Data::MessagePack::PP::Unpacker;

sub new {
    bless {
        pos  => 0,
        utf8 => 0,
        buff => '',
    }, shift;
}

sub utf8 {
    my $self = shift;
    $self->{utf8} = (@_ ? shift : 1);
    return $self;
}

sub get_utf8 {
    my($self) = @_;
    return $self->{utf8};
}

sub execute_limit {
    execute( @_ );
}

sub execute {
    my ( $self, $data, $offset, $limit ) = @_;
    $offset ||= 0;
    my $value = substr( $data, $offset, $limit ? $limit : length $data );
    my $len   = length $value;

    $self->{buff} .= $value;
    local $self->{stack} = [];

    #$p = 0;
    #eval { Data::MessagePack::PP::_unpack($self->{buff}) };
    #warn "[$p][$@]";
    $p = 0;

    while ( length($self->{buff}) > $p ) {
        _count( $self, $self->{buff} ) or last;

        while ( @{ $self->{stack} } > 0 && --$self->{stack}->[-1] == 0) {
            pop @{ $self->{stack} };
        }

        if (@{$self->{stack}} == 0) {
            $self->{is_finished}++;
            last;
        }
    }
    $self->{pos} = $p;

    return $p + $offset;
}


sub _count {
    my ( $self, $value ) = @_;
    my $byte = unpack( 'C', substr( $value, $p++, 1 ) ); # get header

    Carp::croak('invalid data') unless defined $byte;

    # +/- fixnum, nil, true, false
    return 1 if $typemap[$byte] & $T_DIRECT;

    if ( $typemap[$byte] & $T_RAW ) {
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
    elsif ( $typemap[$byte] & $T_ARRAY ) {
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

        if ( $num ) {
            push @{ $self->{stack} }, $num + 1;
        }

        return 1;
    }
    elsif ( $typemap[$byte] & $T_MAP ) {
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

        if ( $num ) {
            push @{ $self->{stack} }, $num * 2 + 1; # a pair
        }

        return 1;
    }

    elsif ( $byte >= 0xcc and $byte <= 0xcf ) { # uint
        $p += $byte == 0xcc ? 1
            : $byte == 0xcd ? 2
            : $byte == 0xce ? 4
            : $byte == 0xcf ? 8
            : Data::MessagePack::PP::_unexpected("byte 0x%02x", $byte);
        return 1;
    }

    elsif ( $byte >= 0xd0 and $byte <= 0xd3 ) { # int
        $p += $byte == 0xd0 ? 1
            : $byte == 0xd1 ? 2
            : $byte == 0xd2 ? 4
            : $byte == 0xd3 ? 8
            : Data::MessagePack::PP::_unexpected("byte 0x%02x", $byte);
        return 1;
    }
    elsif ( $byte == 0xca or $byte == 0xcb ) { # float, double
        $p += $byte == 0xca ? 4 : 8;
        return 1;
    }
    else {
        Data::MessagePack::PP::_unexpected("byte 0x%02x", $byte);
    }

    return 0;
}


sub data {
    my($self) = @_;
    local $Data::MessagePack::PP::_utf8 = $self->{utf8};
    return Data::MessagePack->unpack( substr($self->{buff}, 0, $self->{pos}) );
}


sub is_finished {
    my ( $self ) = @_;
    return $self->{is_finished};
}

sub reset :method {
    $_[0]->{buff}        = '';
    $_[0]->{pos}         = 0;
    $_[0]->{is_finished} = 0;
}

1;
__END__

=pod

=head1 NAME

Data::MessagePack::PP - Pure Perl implementation of Data::MessagePack

=head1 DESCRIPTION

This module is used by L<Data::MessagePack> internally.

=head1 SEE ALSO

L<http://msgpack.sourceforge.jp/>,
L<Data::MessagePack>,
L<http://frox25.no-ip.org/~mtve/wiki/MessagePack.html>,

=head1 AUTHOR

makamaka

=head1 COPYRIGHT AND LICENSE

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.

=cut
