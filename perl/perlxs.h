/*
    perlxs.h - Standard XS header file
    Copyright (c) Fuji, Goro (gfx)
*/

#ifdef __cplusplus
extern "C" {
#endif

#define PERL_NO_GET_CONTEXT /* we want efficiency */
#include <EXTERN.h>

#include <perl.h>
#define NO_XSLOCKS /* for exceptions */
#include <XSUB.h>

#ifdef __cplusplus
} /* extern "C" */
#endif

#include "ppport.h"

/* portability stuff not supported by ppport.h yet */

#ifndef STATIC_INLINE /* from 5.13.4 */
#   if defined(__GNUC__) || defined(__cplusplus__) || (defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L))
#       define STATIC_INLINE static inline
#   else
#       define STATIC_INLINE static
#   endif
#endif /* STATIC_INLINE */

#ifndef __attribute__format__
#define __attribute__format__(a,b,c) /* nothing */
#endif

#ifndef LIKELY /* they are just a compiler's hint */
#define LIKELY(x)   (x)
#define UNLIKELY(x) (x)
#endif

#ifndef newSVpvs_share
#define newSVpvs_share(s) Perl_newSVpvn_share(aTHX_ STR_WITH_LEN(s), 0U)
#endif

#ifndef get_cvs
#define get_cvs(name, flags) get_cv(name, flags)
#endif

#ifndef GvNAME_get
#define GvNAME_get GvNAME
#endif
#ifndef GvNAMELEN_get
#define GvNAMELEN_get GvNAMELEN
#endif

#ifndef CvGV_set
#define CvGV_set(cv, gv) (CvGV(cv) = (gv))
#endif

/* general utility */

#if PERL_BCDVERSION >= 0x5008005
#define LooksLikeNumber(x) looks_like_number(x)
#else
#define LooksLikeNumber(x) (SvPOKp(x) ? looks_like_number(x) : (I32)SvNIOKp(x))
#endif

#define newAV_mortal() (AV*)sv_2mortal((SV*)newAV())
#define newHV_mortal() (HV*)sv_2mortal((SV*)newHV())

#define DECL_BOOT(name) EXTERN_C XS(CAT2(boot_, name))
#define CALL_BOOT(name) STMT_START {            \
        PUSHMARK(SP);                           \
        CALL_FPTR(CAT2(boot_, name))(aTHX_ cv); \
    } STMT_END
