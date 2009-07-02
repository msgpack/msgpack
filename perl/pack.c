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
void need(enc_t *enc, STRLEN len);

#define msgpack_pack_user enc_t*

#define msgpack_pack_append_buffer(enc, buf, len) \
    need(enc, len); \
    memcpy(enc->cur, buf, len); \
    enc->cur += len;

#include "msgpack/pack_template.h"

#define _PACK_WRAPPER(t) msgpack_pack_##t
#define PACK_WRAPPER(t) _PACK_WRAPPER(t)
#define INIT_SIZE   32 /* initial scalar size to be allocated */

void need(enc_t *enc, STRLEN len)
{
    if (enc->cur + len >= enc->end) {
        STRLEN cur = enc->cur - (char *)SvPVX (enc->sv);
        SvGROW (enc->sv, cur + (len < (cur >> 2) ? cur >> 2 : len) + 1);
        enc->cur = SvPVX (enc->sv) + cur;
        enc->end = SvPVX (enc->sv) + SvLEN (enc->sv) - 1;
    }
}

static int looks_like_int(const char *str, size_t len) {
    int i;
    for (i=0; i<len; i++) {
        if (!isDIGIT(str[i])) {
            return 0;
        }
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
            const int U32_STRLEN = 10; /* length(0xFFFFFFFF) */

            SV* pref_int = get_sv("Data::MessagePack::PreferInteger", 0);
            if (pref_int && SvTRUE(pref_int) && len <= U32_STRLEN && looks_like_int(cval, len) && SvUV(val) < U32_MAX) {
                PACK_WRAPPER(uint32)(enc, SvUV(val));
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
