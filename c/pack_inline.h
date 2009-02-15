/*
 * MessagePack packing routine for C
 *
 * Copyright (C) 2008 FURUHASHI Sadayuki
 *
 *    Licensed under the Apache License, Version 2.0 (the "License");
 *    you may not use this file except in compliance with the License.
 *    You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 *    Unless required by applicable law or agreed to in writing, software
 *    distributed under the License is distributed on an "AS IS" BASIS,
 *    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *    See the License for the specific language governing permissions and
 *    limitations under the License.
 */
#ifndef PACK_INLINE_H__
#define PACK_INLINE_H__

#include "msgpack/pack.h"

typedef msgpack_pack_t* msgpack_pack_context;

static inline void msgpack_pack_append_buffer(msgpack_pack_t* x, const unsigned char* b, unsigned int l);

#include <string.h>
#include <arpa/inet.h>  /* __BYTE_ORDER */
#include "msgpack/pack/inline_impl.h"

#endif /* pack_inline.h */

