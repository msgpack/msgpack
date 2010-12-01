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
package org.msgpack.template;

import java.io.IOException;
import org.msgpack.*;

public class FloatArrayTemplate implements Template {
	private FloatArrayTemplate() { }

	public void pack(Packer pk, Object target) throws IOException {
		if(!(target instanceof float[])) {
			throw new MessageTypeException();
		}
		float[] array = (float[])target;
		pk.packArray(array.length);
		for(float a : array) {
			pk.pack(a);
		}
	}

	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		int length = pac.unpackArray();
		float[] array;
		if(to != null && to instanceof float[] && ((float[])to).length == length) {
			array = (float[])to;
		} else {
			array = new float[length];
		}
		for(int i=0; i < length; i++) {
			array[i] = pac.unpackFloat();
		}
		return array;
	}

	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		MessagePackObject[] src = from.asArray();
		float[] array;
		if(to != null && to instanceof float[] && ((float[])to).length == src.length) {
			array = (float[])to;
		} else {
			array = new float[src.length];
		}
		for(int i=0; i < src.length; i++) {
			MessagePackObject s = src[i];
			array[i] = s.asFloat();
		}
		return array;
	}

	static public FloatArrayTemplate getInstance() {
		return instance;
	}

	static final FloatArrayTemplate instance = new FloatArrayTemplate();

	static {
		TemplateRegistry.register(float[].class, instance);
	}
}

