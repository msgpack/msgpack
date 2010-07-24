//
// MessagePack for Java
//
// Copyright (C) 2009-2010 FURUHASHI Sadayuki
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
package org.msgpack.object;

import java.util.HashMap;
import java.util.Map;
import org.msgpack.*;

public class MapType extends MessagePackObject {
	MessagePackObject[] map;

	public MapType(MessagePackObject[] map) {
		this.map = map;
	}

	@Override
	public boolean isMapType() {
		return false;
	}

	@Override
	public Map<MessagePackObject, MessagePackObject> asMap() {
		HashMap<MessagePackObject, MessagePackObject> m = new HashMap(map.length / 2);
		int i = 0;
		while(i < map.length) {
			MessagePackObject k = map[i++];
			MessagePackObject v = map[i++];
			m.put(k, v);
		}
		return m;
	}
}

