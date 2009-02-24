/*
 * MessagePack for C dynamic typing routine
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
#include "msgpack/object.h"
#include "msgpack/pack.h"
#include <stdio.h>
#include <inttypes.h>


int msgpack_pack_object(msgpack_packer* pk, msgpack_object d)
{
	switch(d.type) {
	case MSGPACK_OBJECT_NIL:
		return msgpack_pack_nil(pk);

	case MSGPACK_OBJECT_BOOLEAN:
		if(d.via.boolean) {
			return msgpack_pack_true(pk);
		} else {
			return msgpack_pack_false(pk);
		}

	case MSGPACK_OBJECT_POSITIVE_INTEGER:
		return msgpack_pack_uint64(pk, d.via.u64);

	case MSGPACK_OBJECT_NEGATIVE_INTEGER:
		return msgpack_pack_int64(pk, d.via.i64);

	case MSGPACK_OBJECT_DOUBLE:
		return msgpack_pack_double(pk, d.via.dec);

	case MSGPACK_OBJECT_RAW:
		{
			int ret = msgpack_pack_raw(pk, d.via.raw.size);
			if(ret < 0) { return ret; }
			return msgpack_pack_raw_body(pk, d.via.raw.ptr, d.via.raw.size);
		}

	case MSGPACK_OBJECT_ARRAY:
		{
			int ret = msgpack_pack_array(pk, d.via.array.size);
			if(ret < 0) { return ret; }

			msgpack_object* o = d.via.array.ptr;
			msgpack_object* const oend = d.via.array.ptr + d.via.array.size;
			for(; o != oend; ++o) {
				ret = msgpack_pack_object(pk, *o);
				if(ret < 0) { return ret; }
			}

			return 0;
		}

	case MSGPACK_OBJECT_MAP:
		{
			int ret = msgpack_pack_map(pk, d.via.map.size);
			if(ret < 0) { return ret; }

			msgpack_object_kv* kv = d.via.map.ptr;
			msgpack_object_kv* const kvend = d.via.map.ptr + d.via.map.size;
			for(; kv != kvend; ++kv) {
				ret = msgpack_pack_object(pk, kv->key);
				if(ret < 0) { return ret; }
				ret = msgpack_pack_object(pk, kv->val);
				if(ret < 0) { return ret; }
			}

			return 0;
		}

	default:
		return -1;
	}
}


void msgpack_object_print(FILE* out, msgpack_object o)
{
	switch(o.type) {
	case MSGPACK_OBJECT_NIL:
		fprintf(out, "nil");
		break;

	case MSGPACK_OBJECT_BOOLEAN:
		fprintf(out, (o.via.boolean ? "true" : "false"));
		break;

	case MSGPACK_OBJECT_POSITIVE_INTEGER:
		fprintf(out, "%"PRIu64, o.via.u64);
		break;

	case MSGPACK_OBJECT_NEGATIVE_INTEGER:
		fprintf(out, "%"PRIi64, o.via.i64);
		break;

	case MSGPACK_OBJECT_DOUBLE:
		fprintf(out, "%f", o.via.dec);
		break;

	case MSGPACK_OBJECT_RAW:
		fprintf(out, "\"");
		fwrite(o.via.raw.ptr, o.via.raw.size, 1, out);
		fprintf(out, "\"");
		break;

	case MSGPACK_OBJECT_ARRAY:
		fprintf(out, "[");
		if(o.via.array.size != 0) {
			msgpack_object* p = o.via.array.ptr;
			msgpack_object_print(out, *p);
			++p;
			msgpack_object* const pend = o.via.array.ptr + o.via.array.size;
			for(; p < pend; ++p) {
				fprintf(out, ", ");
				msgpack_object_print(out, *p);
			}
		}
		fprintf(out, "]");
		break;
		// FIXME loop optimiziation

	case MSGPACK_OBJECT_MAP:
		fprintf(out, "{");
		if(o.via.map.size != 0) {
			msgpack_object_kv* p = o.via.map.ptr;
			msgpack_object_print(out, p->key);
			fprintf(out, "=>");
			msgpack_object_print(out, p->val);
			++p;
			msgpack_object_kv* const pend = o.via.map.ptr + o.via.map.size;
			for(; p < pend; ++p) {
				fprintf(out, ", ");
				msgpack_object_print(out, p->key);
				fprintf(out, "=>");
				msgpack_object_print(out, p->val);
			}
		}
		fprintf(out, "}");
		break;
		// FIXME loop optimiziation

	default:
		// FIXME
		fprintf(out, "#<UNKNOWN %hu %"PRIu64">", o.type, o.via.u64);
	}
}

