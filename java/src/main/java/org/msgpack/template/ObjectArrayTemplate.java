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

import java.util.List;
import java.util.ArrayList;
import java.io.IOException;
import org.msgpack.*;

public class ObjectArrayTemplate implements Template {
	static void load() { }

	private Template componentTemplate;

	public ObjectArrayTemplate(Template componentTemplate) {
		this.componentTemplate = componentTemplate;
	}

	public Template getcomponentTemplate() {
		return componentTemplate;
	}

	@SuppressWarnings("unchecked")
	public void pack(Packer pk, Object target) throws IOException {
		if(!(target instanceof Object[])) {
			throw new MessageTypeException();
		}
		Object[] array = (Object[])target;
		pk.packArray(array.length);
		for(Object a : array) {
			componentTemplate.pack(pk, a);
		}
	}

	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		int length = pac.unpackArray();
		Object[] array;
		if(to != null && to instanceof Object[] && ((Object[])to).length == length) {
			array = (Object[])to;
		} else {
			array = new Object[length];
		}
		for(int i=0; i < length; i++) {
			array[i] = componentTemplate.unpack(pac, null);
		}
		return array;
	}

	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		MessagePackObject[] src = from.asArray();
		Object[] array;
		if(to != null && to instanceof Object[] && ((Object[])to).length == src.length) {
			array = (Object[])to;
		} else {
			array = new Object[src.length];
		}
		for(int i=0; i < src.length; i++) {
			MessagePackObject s = src[i];
			array[i] = componentTemplate.convert(s, array[i]);
		}
		return array;
	}
}

