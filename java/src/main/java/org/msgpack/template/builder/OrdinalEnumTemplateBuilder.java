//
// MessagePack for Java
//
// Copyright (C) 2009-2011 FURUHASHI Sadayuki
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
package org.msgpack.template.builder;

import java.io.IOException;
import java.lang.reflect.Type;
import java.util.HashMap;
import java.util.Map;

import org.msgpack.AbstractTemplate;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.template.TemplateBuildException;

public class OrdinalEnumTemplateBuilder implements TemplateBuilder{

	static class ReflectionOrdinalEnumTemplate extends AbstractTemplate {
		protected Enum<?>[] entries;
		protected Map<Enum<?>, Integer> reverse;

		ReflectionOrdinalEnumTemplate(Enum<?>[] entries) {
			this.entries = entries;
			this.reverse = new HashMap<Enum<?>, Integer>();
			for(int i=0; i < entries.length; i++) {
				this.reverse.put(entries[i], i);
			}
		}

		public void pack(Packer pk, Object target) throws IOException {
			Integer ord = reverse.get(target);
			if(ord == null) {
				throw new MessageTypeException();
			}
			pk.pack((int)ord);
		}

		public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
			int ord = pac.unpackInt();
			if(entries.length <= ord) {
				throw new MessageTypeException();
			}
			return entries[ord];
		}

		public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
			int ord = from.asInt();
			if(entries.length <= ord) {
				throw new MessageTypeException();
			}
			return entries[ord];
		}
	}

	@Override
	public Template buildTemplate(Type targetType) {
		Class<?> targetClass = (Class<?>)targetType;
		checkOrdinalEnumValidation(targetClass);
		Enum<?>[] entries = (Enum<?>[])targetClass.getEnumConstants();
		
		return new ReflectionOrdinalEnumTemplate(entries);
	}
	private void checkOrdinalEnumValidation(Class<?> targetClass) {
		if(!targetClass.isEnum()) {
			throw new TemplateBuildException("tried to build ordinal enum template of non-enum class");
		}
	}

}
