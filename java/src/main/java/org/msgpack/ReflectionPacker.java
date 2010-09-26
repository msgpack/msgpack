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
package org.msgpack;

import java.io.IOException;
import java.lang.reflect.*;

// FIXME mock-up
public class ReflectionPacker extends ReflectionBase implements MessagePacker {
	private Class<?> klass;

	private ReflectionPacker(Class<?> klass) {
		this.klass = klass;
	}

	static public ReflectionPacker create(Class klass) {
		// FIXME code generation: generates subclass of ReflectionPacker
		//       returned instance will be cached by Packer into CustomPacker
		return new ReflectionPacker(klass);
	}

	public void pack(Packer pk, Object target) throws IOException {
		Field[] fields = klass.getDeclaredFields();
		pk.packArray(fields.length);
		try {
			for(int i=0; i < fields.length; i++) {
				pk.pack(fields[i].get(target));
			}
		} catch(IllegalAccessException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		}
	}
}

