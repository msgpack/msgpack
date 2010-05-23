/*
 * MessagePack for Ruby
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
#include "pack.h"
#include "unpack.h"

static VALUE mMessagePack;

/**
 * Document-module: MessagePack
 *
 * MessagePack is a binary-based efficient object serialization library.
 * It enables to exchange structured objects between many languages like JSON.
 * But unlike JSON, it is very fast and small.
 *
 *   require 'msgpack'
 *   msg = [1,2,3].to_msgpack  #=> "\x93\x01\x02\x03"
 *   MessagePack.unpack(msg)   #=> [1,2,3]
 *
 */
void Init_msgpack(void)
{
	mMessagePack = rb_define_module("MessagePack");
	Init_msgpack_unpack(mMessagePack);
	Init_msgpack_pack(mMessagePack);
}

