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

#define msgpack_pack_user SV*

#define msgpack_pack_append_buffer(user, buf, len) \
    sv_catpvn(user, (const char*)(buf), len);

#include "msgpack/pack_template.h"

#define _PACK_WRAPPER(t) msgpack_pack_##t
#define PACK_WRAPPER(t) _PACK_WRAPPER(t)

static void _msgpack_pack_sv(SV* buf, SV* val) {
    if (val==NULL) {
        msgpack_pack_nil(buf);
        return;
    }

    switch (SvTYPE(val)) {
    case SVt_NULL:
        msgpack_pack_nil(buf);
        break;
    case SVt_IV:
        if (SvIOK_UV(val)) {
            msgpack_pack_uint32(buf, SvUV(val));
        } else {
            PACK_WRAPPER(IVTYPE)(buf, SvIV(val));
        }
        break;
    case SVt_PVNV:
        {
            STRLEN len = 0;
            char *pv = SvPV(val, len);
            if (len == 1 && *pv == '1') {
                msgpack_pack_true(buf);
            } else if (len == 0 && *pv==0) {
                msgpack_pack_false(buf);
            } else {
                msgpack_pack_nil(buf);
            }
        }
        break;
    case SVt_PV:
        {
            STRLEN len;
            char * cval = SvPV(val, len);
            msgpack_pack_raw(buf, len);
            msgpack_pack_raw_body(buf, cval, len);
        }
        break;
    case SVt_NV:
        PACK_WRAPPER(NVTYPE)(buf, SvNV(val));
        break;
    case SVt_PVAV:
        {
            AV* ary = (AV*)val;
            int len = av_len(ary) + 1;
            int i;
            msgpack_pack_array(buf, len);
            for (i=0; i<len; i++) {
                SV** svp = av_fetch(ary, i, 0);
                if (svp) {
                    _msgpack_pack_sv(buf, *svp);
                } else {
                    msgpack_pack_nil(buf);
                }
            }
        }
        break;
    case SVt_PVHV:
        {
            HV* hval = (HV*)val;
            int count = hv_iterinit(hval);
            HE* he;

            msgpack_pack_map(buf, count);

            while (he = hv_iternext(hval)) {
                _msgpack_pack_sv(buf, hv_iterkeysv(he));
                _msgpack_pack_sv(buf, HeVAL(he));
            }
        }
        break;
    case SVt_RV:
        _msgpack_pack_sv(buf, SvRV(val));
        break;
    default:
        sv_dump(val);
        Perl_croak(aTHX_ "msgpack for perl doesn't supported this type: %d\n", SvTYPE(val));
    }
}

XS(xs_pack) {
    dXSARGS;
    PERL_UNUSED_VAR(items);

    SV* buf = newSVpv("", 0);
    SV* val = ST(1);

    _msgpack_pack_sv(buf, val);

    ST(0) = buf;
    XSRETURN(1);
}
