/*
 * MessagePack for C memory pool implementation
 *
 * Copyright (C) 2008-2009 FURUHASHI Sadayuki
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
#ifndef MSGPACK_ZONE_H__
#define MSGPACK_ZONE_H__

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif


struct _msgpack_zone;
typedef struct _msgpack_zone msgpack_zone;

msgpack_zone* msgpack_zone_new();
void msgpack_zone_free(msgpack_zone* z);

void* msgpack_zone_malloc(msgpack_zone* z, size_t size);


#ifdef __cplusplus
}
#endif

#endif /* msgpack/zone.h */

