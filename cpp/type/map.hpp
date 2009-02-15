//
// MessagePack for C++ static resolution routine
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
#ifndef MSGPACK_TYPE_MAP_HPP__
#define MSGPACK_TYPE_MAP_HPP__

#include "msgpack/object.hpp"
#include <map>
#include <vector>
#include <algorithm>

namespace msgpack {


namespace type {

template <typename K, typename V>
class assoc_vector : public std::vector< std::pair<K, V> > {};

namespace detail {
	template <typename K, typename V>
	struct pair_first_less {
		bool operator() (const std::pair<K, V>& x, const std::pair<K, V>& y) const
			{ return x.first < y.first; }
	};
}

}  //namespace type


template <typename K, typename V>
inline type::assoc_vector<K,V>& operator>> (object o, type::assoc_vector<K,V>& v)
{
	if(o.type != type::MAP) { throw type_error(); }
	v.resize(o.via.container.size);
	object* p = o.via.container.ptr;
	object* const pend = o.via.container.ptr + o.via.container.size;
	std::pair<K, V>* it(&v.front());
	for(; p < pend; ++it) {
		p->convert(&it->first);  ++p;
		p->convert(&it->second); ++p;
	}
	std::sort(v.begin(), v.end(), type::detail::pair_first_less<K,V>());
	return v;
}

template <typename Stream, typename K, typename V>
inline packer<Stream>& operator<< (packer<Stream>& o, const type::assoc_vector<K,V>& v)
{
	o.pack_map(v.size());
	for(typename type::assoc_vector<K,V>::const_iterator it(v.begin()), it_end(v.end());
			it != it_end; ++it) {
		o.pack(it->first);
		o.pack(it->second);
	}
	return o;
}


template <typename K, typename V>
inline std::map<K, V> operator>> (object o, std::map<K, V>& v)
{
	if(o.type != type::MAP) { throw type_error(); }
	object* p(o.via.container.ptr);
	object* const pend(o.via.container.ptr + o.via.container.size*2);
	while(p < pend) {
		K key;
		p->convert(&key); ++p;
		typename std::map<K,V>::iterator it(v.find(key));
		if(it != v.end()) {
			V val;
			p->convert(&val); ++p;
			it->insert( std::pair<K,V>(key, val) );
		} else {
			p->convert(&it->second); ++p;
		}
	}
	return v;
}

template <typename Stream, typename K, typename V>
inline packer<Stream>& operator<< (packer<Stream>& o, const std::map<K,V>& v)
{
	o.pack_map(v.size());
	for(typename std::map<K,V>::const_iterator it(v.begin()), it_end(v.end());
			it != it_end; ++it) {
		o.pack(it->first);
		o.pack(it->second);
	}
	return o;
}


template <typename K, typename V>
inline std::multimap<K, V> operator>> (object o, std::multimap<K, V>& v)
{
	if(o.type != type::MAP) { throw type_error(); }
	object* p = o.via.container.ptr;
	object* const pend = o.via.container.ptr + o.via.container.size*2;
	while(p < pend) {
		std::pair<K, V> value;
		p->convert(&value.first);  ++p;
		p->convert(&value.second); ++p;
		v.insert(value);
	}
	return v;
}

template <typename Stream, typename K, typename V>
inline packer<Stream>& operator<< (packer<Stream>& o, const std::multimap<K,V>& v)
{
	o.pack_multimap(v.size());
	for(typename std::multimap<K,V>::const_iterator it(v.begin()), it_end(v.end());
			it != it_end; ++it) {
		o.pack(it->first);
		o.pack(it->second);
	}
	return o;
}


}  // namespace msgpack

#endif /* msgpack/type/map.hpp */

