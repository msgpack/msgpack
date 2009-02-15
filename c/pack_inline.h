#ifndef PACK_INLINE_H__
#define PACK_INLINE_H__

#include "pack.h"

typedef msgpack_pack_t* msgpack_pack_context;

static inline void msgpack_pack_append_buffer(msgpack_pack_t* x, const unsigned char* b, unsigned int l);

#include <string.h>
#include <arpa/inet.h>  /* __BYTE_ORDER */
#include "msgpack/pack/inline_impl.h"

#endif /* pack_inline.h */

