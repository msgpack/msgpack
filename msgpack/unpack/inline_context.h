/*
 * MessagePack unpacking routine
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
#ifndef MSGPACK_UNPACK_INLINE_CONTEXT_H__
#define MSGPACK_UNPACK_INLINE_CONTEXT_H__

#include <stddef.h>
#include <stdint.h>

#ifndef MSG_STACK_SIZE
#define MSG_STACK_SIZE 16
#endif

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
	msgpack_object obj;
	size_t count;
	unsigned int ct;
	union {
		/*const unsigned char* terminal_trail_start;*/
		msgpack_object map_key;
	} tmp;
} msgpack_unpacker_stack;

typedef struct {
	msgpack_unpack_context user;  // must be first
	unsigned int cs;
	size_t trail;
	unsigned int top;
	msgpack_unpacker_stack stack[MSG_STACK_SIZE];
} msgpack_unpacker;

void msgpack_unpacker_init(msgpack_unpacker* ctx);
int msgpack_unpacker_execute(msgpack_unpacker* ctx, const char* data, size_t len, size_t* off);
#define msgpack_unpacker_data(unpacker) (unpacker)->stack[0].obj

#ifdef __cplusplus
}
#endif

#endif /* msgpack/unpack/inline_context.h */

