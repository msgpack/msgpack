/*
 * code is written by tokuhirom.
 * buffer alocation technique is taken from JSON::XS. thanks to mlehmann.
 */
#include "xshelper.h"

#include "msgpack/pack_define.h"

#define msgpack_pack_inline_func(name) \
    static inline void msgpack_pack ## name

#define msgpack_pack_inline_func_cint(name) \
    static inline void msgpack_pack ## name

typedef struct {
    char *cur; /* SvPVX (sv) + current output position */
    char *end; /* SvEND (sv) */
    SV *sv;    /* result scalar */
} enc_t;
static void need(enc_t *enc, STRLEN len);

#define msgpack_pack_user enc_t*

#define msgpack_pack_append_buffer(enc, buf, len) \
    need(enc, len); \
    memcpy(enc->cur, buf, len); \
    enc->cur += len;

#include "msgpack/pack_template.h"

#define INIT_SIZE   32 /* initial scalar size to be allocated */

#if   IVSIZE == 8
#  define PACK_IV msgpack_pack_int64
#  define PACK_UV msgpack_pack_uint64
#elif IVSIZE == 4
#  define PACK_IV msgpack_pack_int32
#  define PACK_UV msgpack_pack_uint32
#elif IVSIZE == 2
#  define PACK_IV msgpack_pack_int16
#  define PACK_UV msgpack_pack_uint16
#else
#  error  "msgpack only supports IVSIZE = 8,4,2 environment."
#endif

#define ERR_NESTING_EXCEEDED "perl structure exceeds maximum nesting level (max_depth set too low?)"


STATIC_INLINE void need(enc_t *enc, STRLEN len)
{
    dTHX;
    if (enc->cur + len >= enc->end) {
        STRLEN cur = enc->cur - (char *)SvPVX (enc->sv);
        sv_grow (enc->sv, cur + (len < (cur >> 2) ? cur >> 2 : len) + 1);
        enc->cur = SvPVX (enc->sv) + cur;
        enc->end = SvPVX (enc->sv) + SvLEN (enc->sv) - 1;
    }
}


static int s_pref_int = 0;

STATIC_INLINE int pref_int_set(pTHX_ SV* sv, MAGIC* mg PERL_UNUSED_DECL) {
    if (SvTRUE(sv)) {
        s_pref_int = 1;
    } else {
        s_pref_int = 0;
    }
    return 0;
}

MGVTBL pref_int_vtbl = {
    NULL,
    pref_int_set,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
#ifdef MGf_LOCAL
    NULL,
#endif
};

void boot_Data__MessagePack_pack(void) {
    dTHX;
    SV* var = get_sv("Data::MessagePack::PreferInteger", 0);
    sv_magicext(var, NULL, PERL_MAGIC_ext, &pref_int_vtbl, NULL, 0);
    SvSETMAGIC(var);
}


STATIC_INLINE int try_int(enc_t* enc, const char *p, size_t len) {
    int negative = 0;
    const char* pe = p + len;
    uint64_t num = 0;

    if (len == 0) { return 0; }

    if (*p == '-') {
        /* length(-0x80000000) == 11 */
        if (len <= 1 || len > 11) { return 0; }
        negative = 1;
        ++p;
    } else {
        /* length(0xFFFFFFFF) == 10 */
        if (len > 10) { return 0; }
    }

#if '9'=='8'+1 && '8'=='7'+1 && '7'=='6'+1 && '6'=='5'+1 && '5'=='4'+1 \
               && '4'=='3'+1 && '3'=='2'+1 && '2'=='1'+1 && '1'=='0'+1
    do {
        unsigned int c = ((int)*(p++)) - '0';
        if (c > 9) { return 0; }
        num = num * 10 + c;
    } while(p < pe);
#else
    do {
        switch (*(p++)) {
        case '0': num = num * 10 + 0; break;
        case '1': num = num * 10 + 1; break;
        case '2': num = num * 10 + 2; break;
        case '3': num = num * 10 + 3; break;
        case '4': num = num * 10 + 4; break;
        case '5': num = num * 10 + 5; break;
        case '6': num = num * 10 + 6; break;
        case '7': num = num * 10 + 7; break;
        case '8': num = num * 10 + 8; break;
        case '9': num = num * 10 + 9; break;
        default: return 0;
        }
    } while(p < pe);
#endif

    if (negative) {
        if (num > 0x80000000) { return 0; }
        msgpack_pack_int32(enc, ((int32_t)num) * -1);
    } else {
        if (num > 0xFFFFFFFF) { return 0; }
        msgpack_pack_uint32(enc, (uint32_t)num);
    }

    return 1;
}


static void _msgpack_pack_rv(enc_t *enc, SV* sv, int depth);

STATIC_INLINE void _msgpack_pack_sv(enc_t* const enc, SV* const sv, int const depth) {
    dTHX;
    assert(sv);
    if (UNLIKELY(depth <= 0)) Perl_croak(aTHX_ ERR_NESTING_EXCEEDED);
    SvGETMAGIC(sv);

    if (SvPOKp(sv)) {
        STRLEN const len     = SvCUR(sv);
        const char* const pv = SvPVX_const(sv);

        if (s_pref_int && try_int(enc, pv, len)) {
            return;
        } else {
            msgpack_pack_raw(enc, len);
            msgpack_pack_raw_body(enc, pv, len);
        }
    } else if (SvNIOKp(sv)) {
        if(SvUOK(sv)) {
            PACK_UV(enc, SvUVX(sv));
        }
        else if(SvIOKp(sv)) {
            PACK_IV(enc, SvIVX(sv));
        }
        else {
            /* XXX long double is not supported yet. */
            msgpack_pack_double(enc, (double)SvNVX(sv));
        }
    } else if (SvROK(sv)) {
        _msgpack_pack_rv(enc, SvRV(sv), depth-1);
    } else if (!SvOK(sv)) {
        msgpack_pack_nil(enc);
    } else if (isGV(sv)) {
        Perl_croak(aTHX_ "msgpack cannot pack the GV\n");
    } else {
        sv_dump(sv);
        Perl_croak(aTHX_ "msgpack for perl doesn't supported this type: %d\n", SvTYPE(sv));
    }
}

STATIC_INLINE void _msgpack_pack_rv(enc_t *enc, SV* sv, int depth) {
    svtype svt;
    dTHX;
    assert(sv);
    SvGETMAGIC(sv);
    svt = SvTYPE(sv);

    if (SvOBJECT (sv)) {
        HV *stash = gv_stashpv ("Data::MessagePack::Boolean", 1); // TODO: cache?
        if (SvSTASH (sv) == stash) {
            if (SvIV(sv)) {
                msgpack_pack_true(enc);
            } else {
                msgpack_pack_false(enc);
            }
        } else {
            croak ("encountered object '%s', Data::MessagePack doesn't allow the object",
                           SvPV_nolen(sv_2mortal(newRV_inc(sv))));
        }
    } else if (svt == SVt_PVHV) {
        HV* hval = (HV*)sv;
        int count = hv_iterinit(hval);
        HE* he;

        msgpack_pack_map(enc, count);

        while ((he = hv_iternext(hval))) {
            _msgpack_pack_sv(enc, hv_iterkeysv(he), depth);
            _msgpack_pack_sv(enc, HeVAL(he), depth);
        }
    } else if (svt == SVt_PVAV) {
        AV* ary = (AV*)sv;
        int len = av_len(ary) + 1;
        int i;
        msgpack_pack_array(enc, len);
        for (i=0; i<len; i++) {
            SV** svp = av_fetch(ary, i, 0);
            if (svp) {
                _msgpack_pack_sv(enc, *svp, depth);
            } else {
                msgpack_pack_nil(enc);
            }
        }
    } else if (svt < SVt_PVAV) {
        STRLEN len = 0;
        char *pv = svt ? SvPV (sv, len) : 0;

        if (len == 1 && *pv == '1')
            msgpack_pack_true(enc); 
        else if (len == 1 && *pv == '0')
            msgpack_pack_false(enc); 
        else {
            sv_dump(sv);
            croak("cannot encode reference to scalar '%s' unless the scalar is 0 or 1",
                    SvPV_nolen (sv_2mortal (newRV_inc (sv))));
        }
    } else {
        croak ("encountered %s, but msgpack can only represent references to arrays or hashes",
                   SvPV_nolen (sv_2mortal (newRV_inc (sv))));
    }
}

XS(xs_pack) {
    dXSARGS;
    if (items < 2) {
        Perl_croak(aTHX_ "Usage: Data::MessagePack->pack($dat [,$max_depth])");
    }

    SV* val   = ST(1);
    int depth = 512;
    if (items >= 3) depth = SvIV(ST(2));

    enc_t enc;
    enc.sv        = sv_2mortal(newSV(INIT_SIZE));
    enc.cur       = SvPVX(enc.sv);
    enc.end       = SvEND(enc.sv);
    SvPOK_only(enc.sv);

    _msgpack_pack_sv(&enc, val, depth);

    SvCUR_set(enc.sv, enc.cur - SvPVX (enc.sv));
    *SvEND (enc.sv) = 0; /* many xs functions expect a trailing 0 for text strings */

    ST(0) = enc.sv;
    XSRETURN(1);
}
