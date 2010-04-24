//
// MessagePack for C++ dynamic typed objects
//
// Copyright (C) 2008-2009 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
#include "msgpack/object.hpp"
#include <string.h>

namespace msgpack {


std::ostream& operator<< (std::ostream& s, const object o)
{
	switch(o.type) {
	case type::NIL:
		s << "nil";
		break;

	case type::BOOLEAN:
		s << (o.via.boolean ? "true" : "false");
		break;

	case type::POSITIVE_INTEGER:
		s << o.via.u64;
		break;

	case type::NEGATIVE_INTEGER:
		s << o.via.i64;
		break;

	case type::DOUBLE:
		s << o.via.dec;
		break;

	case type::RAW:
		(s << '"').write(o.via.raw.ptr, o.via.raw.size) << '"';
		break;

	case type::ARRAY:
		s << "[";
		if(o.via.array.size != 0) {
			object* p(o.via.array.ptr);
			s << *p;
			++p;
			for(object* const pend(o.via.array.ptr + o.via.array.size);
					p < pend; ++p) {
				s << ", " << *p;
			}
		}
		s << "]";
		break;
		// FIXME loop optimiziation

	case type::MAP:
		s << "{";
		if(o.via.map.size != 0) {
			object_kv* p(o.via.map.ptr);
			s << p->key << "=>" << p->val;
			++p;
			for(object_kv* const pend(o.via.map.ptr + o.via.map.size);
					p < pend; ++p) {
				s << ", " << p->key << "=>" << p->val;
			}
		}
		s << "}";
		break;
		// FIXME loop optimiziation

	default:
		// FIXME
		s << "#<UNKNOWN " << (uint16_t)o.type << ">";
	}
	return s;
}


bool operator==(const object x, const object y)
{
	if(x.type != y.type) { return false; }

	switch(x.type) {
	case type::NIL:
		return true;

	case type::BOOLEAN:
		return x.via.boolean == y.via.boolean;

	case type::POSITIVE_INTEGER:
		return x.via.u64 == y.via.u64;

	case type::NEGATIVE_INTEGER:
		return x.via.i64 == y.via.i64;

	case type::DOUBLE:
		return x.via.dec == y.via.dec;

	case type::RAW:
		return x.via.raw.size == y.via.raw.size &&
			memcmp(x.via.raw.ptr, y.via.raw.ptr, x.via.raw.size) == 0;

	case type::ARRAY:
		if(x.via.array.size != y.via.array.size) { return false; }
		for(object* px(x.via.array.ptr),
				* const pxend(x.via.array.ptr + x.via.array.size),
				* py(y.via.array.ptr);
				px < pxend; ++px, ++py) {
			if(*px != *py) { return false; }
		}
		return true;
		// FIXME loop optimiziation

	case type::MAP:
		if(x.via.map.size != y.via.map.size) { return false; }
		for(object_kv* px(x.via.map.ptr),
				* const pxend(x.via.map.ptr + x.via.map.size),
				* py(y.via.map.ptr);
				px < pxend; ++px, ++py) {
			if(px->key != py->key || px->val != py->val) { return false; }
		}
		return true;

	default:
		return false;
	}
}


}  // namespace msgpack

