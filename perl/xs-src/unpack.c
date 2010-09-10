#ifdef __cplusplus
extern "C" {
#endif

#define NEED_newRV_noinc
#define NEED_sv_2pv_flags
#include "perlxs.h"

#ifdef __cplusplus
};
#endif

typedef struct {
    int finished;
    SV* source;
    int incremented;
} unpack_user;

#include "msgpack/unpack_define.h"

#define msgpack_unpack_struct(name) \
    struct template ## name

#define msgpack_unpack_func(ret, name) \
    ret template ## name

#define msgpack_unpack_callback(name) \
    template_callback ## name

#define msgpack_unpack_object SV*

#define msgpack_unpack_user unpack_user

/* ---------------------------------------------------------------------- */
/* utility functions                                                      */

STATIC_INLINE SV *
get_bool (const char *name) {
    SV * sv = sv_mortalcopy(get_sv( name, 1 ));

    SvREADONLY_on(sv);
    SvREADONLY_on( SvRV(sv) );

    return sv;
}

/* ---------------------------------------------------------------------- */

struct template_context;
typedef struct template_context msgpack_unpack_t;

static void template_init(msgpack_unpack_t* u);

static SV* template_data(msgpack_unpack_t* u);

static int template_execute(msgpack_unpack_t* u,
    const char* data, size_t len, size_t* off);

STATIC_INLINE SV* template_callback_root(unpack_user* u)
{ return &PL_sv_undef; }

STATIC_INLINE int template_callback_uint8(unpack_user* u, uint8_t d, SV** o)
{ *o = sv_2mortal(newSVuv(d)); return 0; }

STATIC_INLINE int template_callback_uint16(unpack_user* u, uint16_t d, SV** o)
{ *o = sv_2mortal(newSVuv(d)); return 0; }

STATIC_INLINE int template_callback_uint32(unpack_user* u, uint32_t d, SV** o)
{ *o = sv_2mortal(newSVuv(d)); return 0; }

STATIC_INLINE int template_callback_uint64(unpack_user* u, uint64_t d, SV** o)
{
#if IVSIZE==4
    *o = sv_2mortal(newSVnv(d));
#else
    *o = sv_2mortal(newSVuv(d));
#endif
    return 0;
}

STATIC_INLINE int template_callback_int8(unpack_user* u, int8_t d, SV** o)
{ *o = sv_2mortal(newSViv((long)d)); return 0; }

STATIC_INLINE int template_callback_int16(unpack_user* u, int16_t d, SV** o)
{ *o = sv_2mortal(newSViv((long)d)); return 0; }

STATIC_INLINE int template_callback_int32(unpack_user* u, int32_t d, SV** o)
{ *o = sv_2mortal(newSViv((long)d)); return 0; }

STATIC_INLINE int template_callback_int64(unpack_user* u, int64_t d, SV** o)
{ *o = sv_2mortal(newSViv(d)); return 0; }

STATIC_INLINE int template_callback_float(unpack_user* u, float d, SV** o)
{ *o = sv_2mortal(newSVnv(d)); return 0; }

STATIC_INLINE int template_callback_double(unpack_user* u, double d, SV** o)
{ *o = sv_2mortal(newSVnv(d)); return 0; }

/* &PL_sv_undef is not so good. see http://gist.github.com/387743 */
STATIC_INLINE int template_callback_nil(unpack_user* u, SV** o)
{ *o = sv_newmortal(); return 0; }

STATIC_INLINE int template_callback_true(unpack_user* u, SV** o)
{ *o = get_bool("Data::MessagePack::true") ; return 0; }

STATIC_INLINE int template_callback_false(unpack_user* u, SV** o)
{ *o = get_bool("Data::MessagePack::false") ; return 0; }

STATIC_INLINE int template_callback_array(unpack_user* u, unsigned int n, SV** o)
{ AV* a = (AV*)sv_2mortal((SV*)newAV()); *o = sv_2mortal((SV*)newRV_inc((SV*)a)); av_extend(a, n); return 0; }

STATIC_INLINE int template_callback_array_item(unpack_user* u, SV** c, SV* o)
{ av_push((AV*)SvRV(*c), o); SvREFCNT_inc(o); return 0; }  /* FIXME set value directry RARRAY_PTR(obj)[RARRAY_LEN(obj)++] */

STATIC_INLINE int template_callback_map(unpack_user* u, unsigned int n, SV** o)
{ HV * h = (HV*)sv_2mortal((SV*)newHV()); *o = sv_2mortal(newRV_inc((SV*)h)); return 0; }

STATIC_INLINE int template_callback_map_item(unpack_user* u, SV** c, SV* k, SV* v)
{ hv_store_ent((HV*)SvRV(*c), k, v, 0); SvREFCNT_inc(v); return 0; }

STATIC_INLINE int template_callback_raw(unpack_user* u, const char* b, const char* p, unsigned int l, SV** o)
{ *o = sv_2mortal((l==0) ? newSVpv("", 0) : newSVpv(p, l)); return 0; }
/* { *o = newSVpvn_flags(p, l, SVs_TEMP); return 0; }  <= this does not works. */

#define UNPACKER(from, name) \
	msgpack_unpack_t *name; \
    name = INT2PTR(msgpack_unpack_t*, SvROK((from)) ? SvIV(SvRV((from))) : SvIV((from))); \
	if(name == NULL) { \
		Perl_croak(aTHX_ "NULL found for " # name " when shouldn't be."); \
	}

#include "msgpack/unpack_template.h"

SV* _msgpack_unpack(SV* data, int limit) {
    msgpack_unpack_t mp;
    unpack_user u = {0, &PL_sv_undef};
	int ret;
	size_t from = 0;
    STRLEN dlen;
    const char * dptr = SvPV_const(data, dlen);
    SV* obj;

	template_init(&mp);
    mp.user = u;

	mp.user.source = data;
	ret = template_execute(&mp, dptr, (size_t)dlen, &from);
	mp.user.source = &PL_sv_undef;

	obj = template_data(&mp);

	if(ret < 0) {
        Perl_croak(aTHX_ "parse error.");
	} else if(ret == 0) {
        Perl_croak(aTHX_ "insufficient bytes.");
	} else {
		if(from < dlen) {
            Perl_croak(aTHX_ "extra bytes.");
		}
        return obj;
	}
}

XS(xs_unpack_limit) {
    dXSARGS;

    if (items != 3) {
        Perl_croak(aTHX_ "Usage: Data::MessagePack->unpack('datadata', $limit)");
    }

    {
        int limit = SvIV(ST(2));
        ST(0) = _msgpack_unpack(ST(1), limit);
    }
    XSRETURN(1);
}


XS(xs_unpack) {
    dXSARGS;
    msgpack_unpack_t mp;

    if (items != 2) {
        Perl_croak(aTHX_ "Usage: Data::MessagePack->unpack('datadata')");
    }

    {
        ST(0) = _msgpack_unpack(ST(1), sv_len(ST(1)));
    }

    XSRETURN(1);
}

/* ------------------------------ stream -- */
/* http://twitter.com/frsyuki/status/13249304748 */

static void _reset(SV* self) {
	unpack_user u = {0, &PL_sv_undef, 0};

	UNPACKER(self, mp);
	template_init(mp);
	mp->user = u;
}

XS(xs_unpacker_new) {
    dXSARGS;
    if (items != 1) {
        Perl_croak(aTHX_ "Usage: Data::MessagePack::Unpacker->new()");
    }

    SV* self = sv_newmortal();
	msgpack_unpack_t *mp;

    Newx(mp, 1, msgpack_unpack_t);

    sv_setref_pv(self, "Data::MessagePack::Unpacker", mp);
    _reset(self);

    ST(0) = self;
    XSRETURN(1);
}

static SV* _execute_impl(SV* self, SV* data, UV off, I32 limit) {
    UNPACKER(self, mp);

    size_t from = off;
	const char* dptr = SvPV_nolen_const(data);
	long dlen = limit;
	int ret;

	if(from >= dlen) {
        Perl_croak(aTHX_ "offset is bigger than data buffer size.");
	}

	mp->user.source = data;
	ret = template_execute(mp, dptr, (size_t)dlen, &from);
	mp->user.source = &PL_sv_undef;

	if(ret < 0) {
		Perl_croak(aTHX_ "parse error.");
	} else if(ret > 0) {
		mp->user.finished = 1;
		return sv_2mortal(newSVuv(from));
	} else {
		mp->user.finished = 0;
		return sv_2mortal(newSVuv(from));
	}
}

XS(xs_unpacker_execute) {
    dXSARGS;
    if (items != 3) {
        Perl_croak(aTHX_ "Usage: $unpacker->execute_limit(data, off)");
    }

	UNPACKER(ST(0), mp);
    {
        SV* self = ST(0);
        SV* data = ST(1);
        IV  off  = SvIV(ST(2)); /* offset of $data. normaly, 0. */

        ST(0) = _execute_impl(self, data, off, sv_len(data));

        {
            SV * d2 = template_data(mp);
            if (!mp->user.incremented && d2) {
                SvREFCNT_inc(d2);
                mp->user.incremented = 1;
            }
        }
    }

    XSRETURN(1);
}

XS(xs_unpacker_execute_limit) {
    dXSARGS;
    if (items != 4) {
        Perl_croak(aTHX_ "Usage: $unpacker->execute_limit(data, off, limit)");
    }

    SV* self = ST(0);
    SV* data = ST(1);
    IV off   = SvIV(ST(2));
    IV limit = SvIV(ST(3));

    ST(0) = _execute_impl(self, data, off, limit);

    XSRETURN(1);
}

XS(xs_unpacker_is_finished) {
    dXSARGS;
    if (items != 1) {
        Perl_croak(aTHX_ "Usage: $unpacker->is_finished()");
    }

	UNPACKER(ST(0), mp);
    ST(0) = (mp->user.finished) ? &PL_sv_yes : &PL_sv_no;

    XSRETURN(1);
}

XS(xs_unpacker_data) {
    dXSARGS;
    if (items != 1) {
        Perl_croak(aTHX_ "Usage: $unpacker->data()");
    }

	UNPACKER(ST(0), mp);
	ST(0) = sv_2mortal(newSVsv(template_data(mp)));

    XSRETURN(1);
}

XS(xs_unpacker_reset) {
    dXSARGS;
    if (items != 1) {
        Perl_croak(aTHX_ "Usage: $unpacker->reset()");
    }

	UNPACKER(ST(0), mp);
    {
        SV * data = template_data(mp);
        if (data) {
            SvREFCNT_dec(data);
        }
    }
    _reset(ST(0));

    XSRETURN(0);
}

XS(xs_unpacker_destroy) {
    dXSARGS;
    if (items != 1) {
        Perl_croak(aTHX_ "Usage: $unpacker->DESTROY()");
    }

	UNPACKER(ST(0), mp);
    SV * data = template_data(mp);
    if (SvOK(data)) {
        SvREFCNT_dec(data);
    }
    Safefree(mp);

    XSRETURN(0);
}
