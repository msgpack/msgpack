/*
 * code is written by tokuhirom.
 * buffer alocation technique is taken from JSON::XS. thanks to mlehmann.
 */
#ifdef __cplusplus
extern "C" {
#endif
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"
#include "ppport.h"
#ifdef __cplusplus
};
#endif

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

#define _PACK_WRAPPER(t) msgpack_pack_##t
#define PACK_WRAPPER(t) _PACK_WRAPPER(t)
#define INIT_SIZE   32 /* initial scalar size to be allocated */

static void need(enc_t *enc, STRLEN len)
{
    if (enc->cur + len >= enc->end) {
        STRLEN cur = enc->cur - (char *)SvPVX (enc->sv);
        SvGROW (enc->sv, cur + (len < (cur >> 2) ? cur >> 2 : len) + 1);
        enc->cur = SvPVX (enc->sv) + cur;
        enc->end = SvPVX (enc->sv) + SvLEN (enc->sv) - 1;
    }
}


static int s_pref_int = 0;

static int pref_int_set(pTHX_ SV* sv, MAGIC* mg) {
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
    SV* var = get_sv("Data::MessagePack::PreferInteger", 0);
    sv_magicext(var, NULL, PERL_MAGIC_ext, &pref_int_vtbl, NULL, 0);
    SvSETMAGIC(var);
}


static int try_int(enc_t* enc, const char *p, size_t len) {
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


static void _msgpack_pack_sv(enc_t *enc, SV* val) {
    if (val==NULL) {
        msgpack_pack_nil(enc);
        return;
    }

    switch (SvTYPE(val)) {
    case SVt_NULL:
        msgpack_pack_nil(enc);
        break;
    case SVt_IV:
        if (SvIOK_UV(val)) {
            msgpack_pack_uint32(enc, SvUV(val));
        } else {
            PACK_WRAPPER(IVTYPE)(enc, SvIV(val));
        }
        break;
    case SVt_PVNV:
        {
            STRLEN len = 0;
            char *pv = SvPV(val, len);
            if (len == 1 && *pv == '1') {
                msgpack_pack_true(enc);
            } else if (len == 0 && *pv==0) {
                msgpack_pack_false(enc);
            } else {
                msgpack_pack_nil(enc);
            }
        }
        break;
    case SVt_NV:
        PACK_WRAPPER(NVTYPE)(enc, SvNV(val));
        break;
    case SVt_PVAV:
        {
            AV* ary = (AV*)val;
            int len = av_len(ary) + 1;
            int i;
            msgpack_pack_array(enc, len);
            for (i=0; i<len; i++) {
                SV** svp = av_fetch(ary, i, 0);
                if (svp) {
                    _msgpack_pack_sv(enc, *svp);
                } else {
                    msgpack_pack_nil(enc);
                }
            }
        }
        break;
    case SVt_PVHV:
        {
            HV* hval = (HV*)val;
            int count = hv_iterinit(hval);
            HE* he;

            msgpack_pack_map(enc, count);

            while (he = hv_iternext(hval)) {
                _msgpack_pack_sv(enc, hv_iterkeysv(he));
                _msgpack_pack_sv(enc, HeVAL(he));
            }
        }
        break;
    case SVt_RV:
        _msgpack_pack_sv(enc, SvRV(val));
        break;
    default:
        if (SvPOKp(val)) {
            STRLEN len;
            char * cval = SvPV(val, len);

            if (s_pref_int && try_int(enc, cval, len)) {
                return;
            }

            msgpack_pack_raw(enc, len);
            msgpack_pack_raw_body(enc, cval, len);
            return;
        } else {
            sv_dump(val);
            Perl_croak(aTHX_ "msgpack for perl doesn't supported this type: %d\n", SvTYPE(val));
        }
    }
}

XS(xs_pack) {
    dXSARGS;
    if (items != 2) {
        Perl_croak(aTHX_ "Usage: Data::MessagePack->pack($dat)");
    }

    SV* val = ST(1);

    enc_t enc;
    enc.sv        = sv_2mortal(NEWSV(0, INIT_SIZE));
    enc.cur       = SvPVX(enc.sv);
    enc.end       = SvEND(enc.sv);
    SvPOK_only(enc.sv);

    _msgpack_pack_sv(&enc, val);

    SvCUR_set(enc.sv, enc.cur - SvPVX (enc.sv));
    *SvEND (enc.sv) = 0; /* many xs functions expect a trailing 0 for text strings */

    ST(0) = enc.sv;
    XSRETURN(1);
}
