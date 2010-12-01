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

public class LongArrayTemplate implements Template {
	private LongArrayTemplate() { }

	public void pack(Packer pk, Object target) throws IOException {
		if(!(target instanceof long[])) {
			throw new MessageTypeException();
		}
		long[] array = (long[])target;
		pk.packArray(array.length);
		for(long a : array) {
			pk.pack(a);
		}
	}

	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		int length = pac.unpackArray();
		long[] array;
		if(to != null && to instanceof long[] && ((long[])to).length == length) {
			array = (long[])to;
		} else {
			array = new long[length];
		}
		for(int i=0; i < length; i++) {
			array[i] = pac.unpackLong();
		}
		return array;
	}

	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		MessagePackObject[] src = from.asArray();
		long[] array;
		if(to != null && to instanceof long[] && ((long[])to).length == src.length) {
			array = (long[])to;
		} else {
			array = new long[src.length];
		}
		for(int i=0; i < src.length; i++) {
			MessagePackObject s = src[i];
			array[i] = s.asLong();
		}
		return array;
	}

	static public LongArrayTemplate getInstance() {
		return instance;
	}

	static final LongArrayTemplate instance = new LongArrayTemplate();

	static {
		TemplateRegistry.register(long[].class, instance);
	}
}

