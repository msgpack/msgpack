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
import java.lang.reflect.Array;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;

import org.msgpack.AbstractTemplate;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.template.BooleanArrayTemplate;
import org.msgpack.template.DoubleArrayTemplate;
import org.msgpack.template.FloatArrayTemplate;
import org.msgpack.template.IntArrayTemplate;
import org.msgpack.template.LongArrayTemplate;
import org.msgpack.template.ShortArrayTemplate;
import org.msgpack.template.TemplateRegistry;

public class ArrayTemplateBuilder implements TemplateBuilder {

	static class ReflectionObjectArrayTemplate extends AbstractTemplate {
		private Class<?> componentClass;
		private Template elementTemplate;

		public ReflectionObjectArrayTemplate(Class<?> componentClass, Template elementTemplate) {
			this.componentClass = componentClass;
			this.elementTemplate = elementTemplate;
		}

		public void pack(Packer pk, Object target) throws IOException {
			if(!(target instanceof Object[]) || !componentClass.isAssignableFrom(target.getClass().getComponentType())) {
				throw new MessageTypeException();
			}
			Object[] array = (Object[])target;
			int length = array.length;
			pk.packArray(length);
			for(int i=0; i < length; i++) {
				elementTemplate.pack(pk, array[i]);
			}
		}

		public Object unpack(Unpacker pac, Object to) throws IOException {
			int length = pac.unpackArray();
			Object[] array = (Object[])Array.newInstance(componentClass, length);
			for(int i=0; i < length; i++) {
				array[i] = elementTemplate.unpack(pac, null);
			}
			return array;
		}

		public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
			MessagePackObject[] src = from.asArray();
			int length = src.length;
			Object[] array = (Object[])Array.newInstance(componentClass, length);
			for(int i=0; i < length; i++) {
				array[i] = elementTemplate.convert(src[i], null);
			}
			return array;
		}
	}

	static class ReflectionMultidimentionalArrayTemplate extends AbstractTemplate {
		private Class<?> componentClass;
		private Template componentTemplate;

		public ReflectionMultidimentionalArrayTemplate(Class<?> componentClass, Template componentTemplate) {
			this.componentClass = componentClass;
			this.componentTemplate = componentTemplate;
		}

		Class<?> getComponentClass() {
			return componentClass;
		}

		public void pack(Packer pk, Object target) throws IOException {
			Object[] array = (Object[])target;
			int length = array.length;
			pk.packArray(length);
			for(int i=0; i < length; i++) {
				componentTemplate.pack(pk, array[i]);
			}
		}

		public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
			int length = pac.unpackArray();
			Object[] array = (Object[])Array.newInstance(componentClass, length);
			for(int i=0; i < length; i++) {
				array[i] = componentTemplate.unpack(pac, null);
			}
			return array;
		}

		public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
			MessagePackObject[] src = from.asArray();
			int length = src.length;
			Object[] array = (Object[])Array.newInstance(componentClass, length);
			for(int i=0; i < length; i++) {
				array[i] = componentTemplate.convert(src[i], null);
			}
			return array;
		}
	}

	@Override
	public Template buildTemplate(Type arrayType) {
		Type baseType;
		Class<?> baseClass;
		int dim = 1;
		if(arrayType instanceof GenericArrayType) {
			GenericArrayType type = (GenericArrayType)arrayType;
			baseType = type.getGenericComponentType();
			while(baseType instanceof GenericArrayType) {
				baseType = ((GenericArrayType)baseType).getGenericComponentType();
				dim += 1;
			}
			if(baseType instanceof ParameterizedType) {
				baseClass = (Class<?>)((ParameterizedType)baseType).getRawType();
			} else {
				baseClass = (Class<?>)baseType;
			}
		} else {
			Class<?> type = (Class<?>)arrayType;
			baseClass = type.getComponentType();
			while(baseClass.isArray()) {
				baseClass = baseClass.getComponentType();
				dim += 1;
			}
			baseType = baseClass;
		}
		return toTemplate(arrayType, baseType, baseClass, dim);
	
	}

	private Template toTemplate(Type arrayType, Type genericBaseType, Class<?> baseClass, int dim) {
		if(dim == 1) {
			if(baseClass == boolean.class) {
				return BooleanArrayTemplate.getInstance();
			} else if(baseClass == short.class) {
				return ShortArrayTemplate.getInstance();
			} else if(baseClass == int.class) {
				return IntArrayTemplate.getInstance();
			} else if(baseClass == long.class) {
				return LongArrayTemplate.getInstance();
			} else if(baseClass == float.class) {
				return FloatArrayTemplate.getInstance();
			} else if(baseClass == double.class) {
				return DoubleArrayTemplate.getInstance();
			} else {
				Template baseTemplate = TemplateRegistry.lookup(genericBaseType);
				return new ReflectionObjectArrayTemplate(baseClass, baseTemplate);
			}
		} else if(dim == 2) {
			Class<?> componentClass = Array.newInstance(baseClass, 0).getClass();
			Template componentTemplate = toTemplate(arrayType, genericBaseType, baseClass, dim-1);
			return new ReflectionMultidimentionalArrayTemplate(componentClass, componentTemplate);
		} else {
			ReflectionMultidimentionalArrayTemplate componentTemplate = (ReflectionMultidimentionalArrayTemplate)
				toTemplate(arrayType, genericBaseType, baseClass, dim-1);
			Class<?> componentClass = Array.newInstance(componentTemplate.getComponentClass(), 0).getClass();
			return new ReflectionMultidimentionalArrayTemplate(componentClass, componentTemplate);
		}
	}

	@Override
	public void writeTemplate(Type targetType, String directoryName) {
		throw new UnsupportedOperationException(targetType.toString());
	}

	@Override
	public Template loadTemplate(Type targetType) {
		return null;
	}
}
