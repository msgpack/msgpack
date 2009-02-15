//
// MessagePack for C++ dynamic typed objects
//
// Copyright (C) 2008 FURUHASHI Sadayuki
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

	case type::RAW:
		(s << '"').write(o.via.ref.ptr, o.via.ref.size) << '"';
		break;

	case type::ARRAY:
		s << "[";
		if(o.via.container.size != 0) {
			object* p(o.via.container.ptr);
			s << *p;
			++p;
			for(object* const pend(o.via.container.ptr + o.via.container.size);
					p < pend; ++p) {
				s << ", " << *p;
			}
		}
		s << "]";
		break;
		// FIXME loop optimiziation

	case type::MAP:
		s << "{";
		if(o.via.container.size != 0) {
			object* p(o.via.container.ptr);
			object* const pend(o.via.container.ptr + o.via.container.size*2);
			s << *p;  ++p;
			s << "=>";
			s << *p;  ++p;
			while(p < pend) {
				s << ", ";
				s << *p;  ++p;
				s << "=>";
				s << *p;  ++p;
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

	case type::RAW:
		return x.via.ref.size == y.via.ref.size &&
			memcmp(x.via.ref.ptr, y.via.ref.ptr, x.via.ref.size) == 0;

	case type::ARRAY:
		if(x.via.container.size != y.via.container.size) { return false; }
		for(object* px(x.via.container.ptr),
				* const pxend(x.via.container.ptr + x.via.container.size),
				* py(y.via.container.ptr);
				px < pxend; ++px, ++py) {
			if(*px != *py) { return false; }
		}
		return true;
		// FIXME loop optimiziation

	case type::MAP:
		if(x.via.container.size != y.via.container.size) { return false; }
		for(object* px(x.via.container.ptr),
				* const pxend(x.via.container.ptr + x.via.container.size*2),
				* py(y.via.container.ptr);
				px < pxend; ++px, ++py) {
			if(*px != *py) { return false; }
		}
		return true;

	default:
		return false;
	}
}


}  // namespace msgpack

