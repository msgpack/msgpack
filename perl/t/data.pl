no warnings; # i need this, i need this.
(
    '93 c0 c2 c3' => [undef, false, true],
    '94 a0 a1 61 a2 62 63 a3 64 65 66', ["", "a", "bc", "def"],
    '92 90 91 91 c0', [[], [[undef]]],
    '93 c0 c2 c3', [undef, false, true],

    '82             d0 2a c2 d0 2b c3', { 42 => false, 43 => true }, # fix map
    'de       00 02 d0 2a c2 d0 2b c3', { 42 => false, 43 => true }, # map 16
    'df 00 00 00 02 d0 2a c2 d0 2b c3', { 42 => false, 43 => true }, # map 32

    'ce 80 00 00 00', 2147483648,
    '99 cc 00 cc 80 cc ff cd 00 00 cd 80 00 cd ff ff ce 00 00 00 00 ce 80 00 00 00 ce ff ff ff ff',
        [0, 128, 255, 0, 32768, 65535, 0, 2147483648, 4294967295],
    '92 93 00 40 7f 93 e0 f0 ff', [[0, 64, 127], [-32, -16, -1]],
    '96 dc 00 00 dc 00 01 c0 dc 00 02 c2 c3 dd 00 00 00 00 dd 00 00 00 01 c0 dd 00 00 00 02 c2 c3',
        [[], [undef], [false, true], [], [undef], [false, true]],
    '96 da 00 00 da 00 01 61 da 00 02 61 62 db 00 00 00 00 db 00 00 00 01 61 db 00 00 00 02 61 62',
        ["", "a", "ab", "", "a", "ab"],
    '99 d0 00 d0 80 d0 ff d1 00 00 d1 80 00 d1 ff ff d2 00 00 00 00 d2 80 00 00 00 d2 ff ff ff ff',
        [0, -128, -1, 0, -32768, -1, 0, -2147483648, -1],
    '82 c2 81 c0 c0 c3 81 c0 80', {false,{undef,undef}, true,{undef,{}}},
    '96 de 00 00 de 00 01 c0 c2 de 00 02 c0 c2 c3 c2 df 00 00 00 00 df 00 00 00 01 c0 c2 df 00 00 00 02 c0 c2 c3 c2',
        [{}, {undef,false}, {true,false, undef,false}, {}, {undef,false}, {true,false, undef,false}],
    'ce 00 ff ff ff' => ''.0xFFFFFF,
    'aa 34 32 39 34 39 36 37 32 39 35' => ''.0xFFFFFFFF,
    'ab 36 38 37 31 39 34 37 36 37 33 35' => ''.0xFFFFFFFFF,

    'd2 80 00 00 01' => '-2147483647', # int32_t
    'ce 80 00 00 01' => '2147483649',  # uint32_t

    'd2 ff ff ff ff' => '-1',          # int32_t
    'ce ff ff ff ff' => '4294967295',  # uint32_t

    'd3 00 00 00 00 80 00 00 01' => '2147483649', # int64_t
    'cf 00 00 00 00 80 00 00 01' => '2147483649',  # uint64_t

    'd3 ff 00 ff ff ff ff ff ff' => '-71776119061217281',    # int64_t
    'cf ff 00 ff ff ff ff ff ff' => '18374967954648334335',  # uint64_t

    'd3 ff ff ff ff ff ff ff ff' => '-1',                    # int64_t
    'cf ff ff ff ff ff ff ff ff' => '18446744073709551615',  # uint64_t

    # int64_t
    'd3 00 00 00 10 00 00 00 00' => '68719476736',
    'd3 00 00 00 10 00 00 00 01' => '68719476737',
    'd3 00 00 10 00 00 00 00 00' => '17592186044416',
    'd3 00 10 00 00 00 00 00 00' => '4503599627370496',
    'd3 10 00 00 00 00 00 00 00' => '1152921504606846976',
    'd3 11 00 00 00 00 00 00 00' => '1224979098644774912',
)
