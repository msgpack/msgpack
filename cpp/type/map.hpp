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

template <typename K, typename V>
inline assoc_vector<K,V>& operator<< (assoc_vector<K,V>& v, object o)
{
	if(o.type != MAP) { throw type_error(); }
	v.resize(o.via.container.size);
	object* p(o.via.container.ptr);
	object* const pend(o.via.container.ptr + o.via.container.size);
	std::pair<K, V>* it(&v.front());
	for(; p < pend; ++it) {
		convert(it->first,  *p); ++p;
		convert(it->second, *p); ++p;
	}
	std::sort(v.begin(), v.end(), detail::pair_first_less<K,V>());
	return v;
}

template <typename Stream, typename K, typename V>
inline const assoc_vector<K,V>& operator>> (const assoc_vector<K,V>& v, packer<Stream>& o)
{
	o.pack_map(v.size());
	for(typename assoc_vector<K,V>::const_iterator it(v.begin()), it_end(v.end());
			it != it_end; ++it) {
		pack(it->first, o);
		pack(it->second, o);
	}
}


template <typename K, typename V>
inline std::map<K, V> operator<< (std::map<K, V>& v, object o)
{
	if(o.type != MAP) { throw type_error(); }
	object* p(o.via.container.ptr);
	object* const pend(o.via.container.ptr + o.via.container.size*2);
	while(p < pend) {
		K key;
		convert(key, *p);  ++p;
		typename std::map<K,V>::iterator it(v.find(key));
		if(it != v.end()) {
			V val;
			convert(val, *p);  ++p;
			it->insert( std::pair<K,V>(key, val) );
		} else {
			convert(it->second, *p); ++p;
		}
	}
	return v;
}

template <typename Stream, typename K, typename V>
inline const std::map<K,V>& operator>> (const std::map<K,V>& v, packer<Stream>& o)
{
	o.pack_map(v.size());
	for(typename std::map<K,V>::const_iterator it(v.begin()), it_end(v.end());
			it != it_end; ++it) {
		pack(it->first, o);
		pack(it->second, o);
	}
}


template <typename K, typename V>
inline std::multimap<K, V> operator<< (std::multimap<K, V>& v, object o)
{
	if(o.type != MAP) { throw type_error(); }
	object* p(o.via.container.ptr);
	object* const pend(o.via.container.ptr + o.via.container.size*2);
	while(p < pend) {
		std::pair<K, V> value;
		convert(value.first, *p);  ++p;
		convert(value.second, *p);  ++p;
		v.insert(value);
	}
	return v;
}

template <typename Stream, typename K, typename V>
inline const std::multimap<K,V>& operator>> (const std::multimap<K,V>& v, packer<Stream>& o)
{
	o.pack_multimap(v.size());
	for(typename std::multimap<K,V>::const_iterator it(v.begin()), it_end(v.end());
			it != it_end; ++it) {
		pack(it->first, o);
		pack(it->second, o);
	}
}


}  // namespace type
}  // namespace msgpack

#endif /* msgpack/type/map.hpp */

