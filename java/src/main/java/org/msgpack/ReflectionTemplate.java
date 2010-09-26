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
import org.msgpack.template.ClassTemplate;

// FIXME mock-up
public class ReflectionTemplate extends ReflectionBase implements Template {
	private Class klass;

	private ReflectionTemplate(Class klass) {
		this.klass = klass;
	}

	static public ReflectionTemplate create(Class klass) {
		// FIXME code generation: generates subclass of ReflectionPacker
		//       returned instance will be cached by ClassTemplate into CustomUnpacker/CustomConverter
		return new ReflectionTemplate(klass);
	}

	public Object unpack(Unpacker pac) throws IOException, MessageTypeException {
		// FIXME optimize it
		return convert(pac.unpackObject());
	}

	public Object convert(MessagePackObject from) throws MessageTypeException {
		Object obj;
		try {
			obj = klass.newInstance();
		} catch (IllegalAccessException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		} catch (InstantiationException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		}

		// FIXME check Requred/Optional

		Field[] fields = klass.getDeclaredFields();
		MessagePackObject[] array = from.asArray();
		if(fields.length < array.length) {
			throw new MessageTypeException();
		}

		try {
			for(int i=0; i < fields.length; i++) {
				// FIXME generics getDeclaringClass
				Object value = new ClassTemplate(fields[i].getType()).convert(array[i]);
				fields[i].set(obj, value);
			}
		} catch(IllegalAccessException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		}

		return obj;
	}
}

