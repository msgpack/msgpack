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

import java.util.Collection;
import java.util.LinkedList;
import java.io.IOException;

import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

public class CollectionTemplate implements Template {
	public static void load() { }

	private Template elementTemplate;

	public CollectionTemplate(Template elementTemplate) {
		this.elementTemplate = elementTemplate;
	}

	@SuppressWarnings("unchecked")
	public void pack(Packer pk, Object target) throws IOException {
		if (! (target instanceof Collection)) {
			if (target == null) {
				throw new MessageTypeException(new NullPointerException("target is null."));
			}
			throw new MessageTypeException("target is not Collection type: " + target.getClass());
		}
		Collection<Object> collection = (Collection<Object>) target;
		pk.packArray(collection.size());
		for(Object element : collection) {
			elementTemplate.pack(pk, element);
		}
	}

	@SuppressWarnings("unchecked")
	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		int length = pac.unpackArray();
		Collection<Object> c;
		if(to == null) {
			c = new LinkedList<Object>();
		} else {
			// TODO: optimize if list is instanceof ArrayList
			c = (Collection<Object>) to;
			c.clear();
		}
		for(; length > 0; length--) {
			c.add(elementTemplate.unpack(pac, null));
		}
		return c;
	}

	@SuppressWarnings("unchecked")
	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		MessagePackObject[] array = from.asArray();
		Collection<Object> c;
		if(to == null) {
			c = new LinkedList<Object>();
		} else {
			// TODO: optimize if list is instanceof ArrayList
			c = (Collection<Object>) to;
			c.clear();
		}
		for(MessagePackObject element : array) {
			c.add(elementTemplate.convert(element, null));
		}
		return c;
	}

	static {
		TemplateRegistry.registerGeneric(Collection.class, new GenericTemplate1(CollectionTemplate.class));
		TemplateRegistry.register(Collection.class, new CollectionTemplate(AnyTemplate.getInstance()));
	}
}

