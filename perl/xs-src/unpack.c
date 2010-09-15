#define NEED_newRV_noinc
#define NEED_sv_2pv_flags
#include "xshelper.h"

typedef struct {
    bool finished;
    bool incremented;
} unpack_user;

#include "msgpack/unpack_define.h"

#define msgpack_unpack_struct(name) \
    struct template ## name

#define msgpack_unpack_func(ret, name) \
    STATIC_INLINE ret template ## name

#define msgpack_unpack_callback(name) \
    template_callback ## name

#define msgpack_unpack_object SV*

#define msgpack_unpack_user unpack_user

/* ---------------------------------------------------------------------- */
/* utility functions                                                      */

STATIC_INLINE SV *
get_bool (const char *name) {
    dTHX;
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

static int template_execute(msgpack_unpack_t* u PERL_UNUSED_DECL,
    const char* data, size_t len, size_t* off);

STATIC_INLINE SV* template_callback_root(unpack_user* u PERL_UNUSED_DECL)
{
    dTHX;
    return &PL_sv_undef;
}

STATIC_INLINE int template_callback_uint8(unpack_user* u PERL_UNUSED_DECL, uint8_t d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSVuv(d));
    return 0;
}

STATIC_INLINE int template_callback_uint16(unpack_user* u PERL_UNUSED_DECL, uint16_t d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSVuv(d));
    return 0;
}

STATIC_INLINE int template_callback_uint32(unpack_user* u PERL_UNUSED_DECL, uint32_t d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSVuv(d));
    return 0;
}

STATIC_INLINE int template_callback_uint64(unpack_user* u PERL_UNUSED_DECL, uint64_t d, SV** o)
{
    dTHX;
#if IVSIZE==4
    *o = sv_2mortal(newSVnv(d));
#else
    *o = sv_2mortal(newSVuv(d));
#endif
    return 0;
}

STATIC_INLINE int template_callback_int8(unpack_user* u PERL_UNUSED_DECL, int8_t d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSViv(d));
    return 0;
}

STATIC_INLINE int template_callback_int16(unpack_user* u PERL_UNUSED_DECL, int16_t d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSViv(d));
    return 0;
}

STATIC_INLINE int template_callback_int32(unpack_user* u PERL_UNUSED_DECL, int32_t d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSViv(d));
    return 0;
}

STATIC_INLINE int template_callback_int64(unpack_user* u PERL_UNUSED_DECL, int64_t d, SV** o)
{
    dTHX;
#if IVSIZE==4
    *o = sv_2mortal(newSVnv(d));
#else
    *o = sv_2mortal(newSViv(d));
#endif
    return 0;
}

STATIC_INLINE int template_callback_float(unpack_user* u PERL_UNUSED_DECL, float d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSVnv(d));
    return 0;
}

STATIC_INLINE int template_callback_double(unpack_user* u PERL_UNUSED_DECL, double d, SV** o)
{
    dTHX;
    *o = sv_2mortal(newSVnv(d));
    return 0;
}

/* &PL_sv_undef is not so good. see http://gist.github.com/387743 */
STATIC_INLINE int template_callback_nil(unpack_user* u PERL_UNUSED_DECL, SV** o)
{
    dTHX;
    *o = sv_newmortal();
    return 0;
}

STATIC_INLINE int template_callback_true(unpack_user* u PERL_UNUSED_DECL, SV** o)
{
    dTHX;
    *o = get_bool("Data::MessagePack::true");
    return 0;
}

STATIC_INLINE int template_callback_false(unpack_user* u PERL_UNUSED_DECL, SV** o)
{
    dTHX; *o = get_bool("Data::MessagePack::false");
    return 0;
}

STATIC_INLINE int template_callback_array(unpack_user* u PERL_UNUSED_DECL, unsigned int n, SV** o)
{
    dTHX;
    AV* const a = newAV();
    *o = sv_2mortal(newRV_noinc((SV*)a));
    av_extend(a, n + 1);
    return 0;
}

STATIC_INLINE int template_callback_array_item(unpack_user* u PERL_UNUSED_DECL, SV** c, SV* o)
{
    dTHX;
    AV* const a = (AV*)SvRV(*c);
    (void)av_store(a, AvFILLp(a) + 1, o); // the same as av_push(a, o)
    SvREFCNT_inc_simple_void_NN(o);
    return 0;
}

STATIC_INLINE int template_callback_map(unpack_user* u PERL_UNUSED_DECL, unsigned int n PERL_UNUSED_DECL, SV** o)
{
    dTHX;
    HV* const h = newHV();
    *o = sv_2mortal(newRV_noinc((SV*)h));
    return 0;
}

STATIC_INLINE int template_callback_map_item(unpack_user* u PERL_UNUSED_DECL, SV** c, SV* k, SV* v)
{
    dTHX;
    (void)hv_store_ent((HV*)SvRV(*c), k, v, 0);
    SvREFCNT_inc_simple_void_NN(v);
    return 0;
}

STATIC_INLINE int template_callback_raw(unpack_user* u PERL_UNUSED_DECL, const char* b PERL_UNUSED_DECL, const char* p, unsigned int l, SV** o)
{
    dTHX;
    /*  newSVpvn_flags(p, l, SVs_TEMP) returns an undef if l == 0 */
    *o = ((l==0) ? newSVpvs_flags("", SVs_TEMP) : newSVpvn_flags(p, l, SVs_TEMP));
    return 0;
}

#define UNPACKER(from, name)                                              \
    msgpack_unpack_t *name;                                               \
    if(!(SvROK(from) && SvIOK(SvRV(from)))) {                             \
        Perl_croak(aTHX_ "Invalid unpacker instance for " #name);         \
    }                                                                     \
    name = INT2PTR(msgpack_unpack_t*, SvIVX(SvRV((from))));               \
    if(name == NULL) {                                                    \
        Perl_croak(aTHX_ "NULL found for " # name " when shouldn't be."); \
    }

#include "msgpack/unpack_template.h"

STATIC_INLINE SV* _msgpack_unpack(SV* data, size_t limit PERL_UNUSED_DECL) {
    msgpack_unpack_t mp;
    dTHX;
    unpack_user u = {false, false};
	int ret;
	size_t from = 0;
    STRLEN dlen;
    const char * dptr = SvPV_const(data, dlen);
    SV* obj;

	template_init(&mp);
    mp.user = u;

	ret = template_execute(&mp, dptr, (size_t)dlen, &from);
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

XS(xs_unpack) {
    dXSARGS;
    SV* const data = ST(1);
    size_t limit;

    if (items == 2) {
        limit = sv_len(data);
    }
    else if(items == 3) {
        limit = SvUVx(ST(2));
    }
    else {
        Perl_croak(aTHX_ "Usage: Data::MessagePack->unpack('data' [, $limit])");
    }

    ST(0) = _msgpack_unpack(data, limit);

    XSRETURN(1);
}

/* ------------------------------ stream -- */
/* http://twitter.com/frsyuki/status/13249304748 */

STATIC_INLINE void _reset(SV* self) {
    dTHX;
	unpack_user u = {false, false};

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

STATIC_INLINE SV* _execute_impl(SV* self, SV* data, UV off, size_t limit) {
    dTHX;
    UNPACKER(self, mp);

    size_t from = off;
	const char* dptr = SvPV_nolen_const(data);
	int ret;

	if(from >= limit) {
        Perl_croak(aTHX_ "offset is bigger than data buffer size.");
	}

	ret = template_execute(mp, dptr, limit, &from);

	if(ret < 0) {
		Perl_croak(aTHX_ "parse error.");
	} else {
		mp->user.finished = (ret > 0) ? true : false;
		return sv_2mortal(newSVuv(from));
	}
}

XS(xs_unpacker_execute) {
    dXSARGS;
    if (items != 3) {
        Perl_croak(aTHX_ "Usage: $unpacker->execute(data, off)");
    }

	UNPACKER(ST(0), mp);
    {
        SV* self = ST(0);
        SV* data = ST(1);
        IV  off  = SvIV(ST(2)); /* offset of $data. normaly, 0. */

        ST(0) = _execute_impl(self, data, off, (size_t)sv_len(data));

        {
            SV * d2 = template_data(mp);
            if (!mp->user.incremented && d2) {
                SvREFCNT_inc(d2);
                mp->user.incremented = true;
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

    ST(0) = _execute_impl(self, data, off, (size_t)limit);

    XSRETURN(1);
}

XS(xs_unpacker_is_finished) {
    dXSARGS;
    if (items != 1) {
        Perl_croak(aTHX_ "Usage: $unpacker->is_finished()");
    }

	UNPACKER(ST(0), mp);
    ST(0) = boolSV(mp->user.finished);

    XSRETURN(1);
}

XS(xs_unpacker_data) {
    dXSARGS;
    if (items != 1) {
        Perl_croak(aTHX_ "Usage: $unpacker->data()");
    }

	UNPACKER(ST(0), mp);
	ST(0) = sv_mortalcopy(template_data(mp));

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
