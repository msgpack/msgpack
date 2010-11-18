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
package org.msgpack.util.codegen;

import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtField;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.LoaderClassPath;
import javassist.NotFoundException;

import org.msgpack.CustomConverter;
import org.msgpack.CustomMessage;
import org.msgpack.MessageConvertable;
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePackable;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Templates;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackDelegate;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class DynamicCodeGenBase implements Constants {

	private static Logger LOG = LoggerFactory
			.getLogger(DynamicCodeGenBase.class);

	static class MessagePackUnpackConvertableTemplate implements Template {
		private Class<?> type;

		MessagePackUnpackConvertableTemplate(Class<?> type) {
			this.type = type;
		}

		@Override
		public void pack(Packer packer, Object target) throws IOException {
			MessagePackable mp = MessagePackable.class.cast(target);
			mp.messagePack(packer);
		}

		@Override
		public Object unpack(Unpacker unpacker, Object to) throws IOException,
				MessageTypeException {
			try {
				MessageUnpackable obj;
				if(to == null) {
					obj = (MessageUnpackable) type.newInstance();
				} else {
					obj = (MessageUnpackable) to;
				}
				obj.messageUnpack(unpacker);
				return obj;
			} catch (ClassCastException e) {
				throw new MessageTypeException(e.getMessage(), e);
			} catch (InstantiationException e) {
				throw new MessageTypeException(e.getMessage(), e);
			} catch (IllegalAccessException e) {
				throw new MessageTypeException(e.getMessage(), e);
			}
		}

		@Override
		public Object convert(MessagePackObject from, Object to)
				throws MessageTypeException {
			try {
				MessageConvertable obj;
				if(to == null) {
					obj = (MessageConvertable) type.newInstance();
				} else {
					obj = (MessageConvertable) to;
				}
				obj.messageConvert(from);
				return obj;
			} catch (ClassCastException e) {
				throw new MessageTypeException(e.getMessage(), e);
			} catch (InstantiationException e) {
				throw new MessageTypeException(e.getMessage(), e);
			} catch (IllegalAccessException e) {
				throw new MessageTypeException(e.getMessage(), e);
			}
		}
	}

	public static interface TemplateAccessor {
		void setTemplates(Template[] templates);
	}

	protected static class TemplateAccessorImpl implements TemplateAccessor {
		public Class<?> type;

		public Template[] _$$_templates;

		public TemplateAccessorImpl() {
		}

		public TemplateAccessorImpl(Class<?> type) {
			this.type = type;
		}

		public void setTemplates(Template[] _$$_tmpls) {
			_$$_templates = _$$_tmpls;
		}
	}

	private static AtomicInteger COUNTER = new AtomicInteger(0);

	protected static int inc() {
		return COUNTER.addAndGet(1);
	}

	protected ClassPool pool;

	protected DynamicCodeGenBase() {
		pool = ClassPool.getDefault();
	}

	protected void setClassLoader(ClassLoader cl) {
		pool.appendClassPath(new LoaderClassPath(cl));
	}

	protected void checkTypeValidation(Class<?> type) {
		DynamicCodeGenException e = new DynamicCodeGenException(String.format(
				"Fatal error: %s", new Object[] { type.getName() }));
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void throwTypeValidationException(Class<?> type, String message)
			throws DynamicCodeGenException {
		DynamicCodeGenException e = new DynamicCodeGenException(String.format(
				"%s: %s", new Object[] { message, type.getName() }));
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void checkDefaultConstructorValidation(Class<?> type) {
		DynamicCodeGenException e = new DynamicCodeGenException(String.format(
				"Fatal error: %s", new Object[] { type.getName() }));
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void throwConstructorValidationException(Class<?> origClass) {
		DynamicCodeGenException e = new DynamicCodeGenException(String.format(
				"it must have a public zero-argument constructor: %s",
				new Object[] { origClass.getName() }));
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void throwFieldValidationException(Field field) {
		DynamicCodeGenException e = new DynamicCodeGenException(String.format(
				"it must be a public field: %s",
				new Object[] { field.getName() }));
		LOG.debug(e.getMessage(), e);
		throw e;
	}

	protected void throwFieldSortingException(String message) {
		DynamicCodeGenException e = new DynamicCodeGenException(message);
		LOG.debug(e.getMessage(), e);
		throw e;
	}

	protected static void throwMethodValidationException(Method method,
			String message) throws DynamicCodeGenException {
		DynamicCodeGenException e = new DynamicCodeGenException(String.format(
				"%s: %s", new Object[] { message, method.getName() }));
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected CtClass makeClass(String name) throws NotFoundException {
		DynamicCodeGenException e = new DynamicCodeGenException(String.format(
				"Fatal error: %s", new Object[] { name }));
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void setSuperclass(CtClass newCtClass, Class<?> superClass)
			throws NotFoundException, CannotCompileException {
		// check the specified super class
		if (superClass.isInterface() || superClass.isEnum()
				|| superClass.isAnnotation() || superClass.isArray()
				|| superClass.isPrimitive()) {
			throwTypeValidationException(superClass, "Fatal error");
		}

		// check the base class
		if (!newCtClass.getSuperclass().equals(classToCtClass(Object.class))) {
			throwTypeValidationException(superClass, "Fatal error");
		}
		CtClass superCtClass = pool.get(superClass.getName());
		newCtClass.setSuperclass(superCtClass);
	}

	protected void setInterface(CtClass newCtClass, Class<?> infClass)
			throws NotFoundException {
		CtClass infCtClass = pool.get(infClass.getName());
		newCtClass.addInterface(infCtClass);
	}

	protected void addClassTypeConstructor(CtClass newCtClass)
			throws CannotCompileException, NotFoundException {
		CtConstructor newCtCons = CtNewConstructor.make(new CtClass[] { pool
				.get(Class.class.getName()) }, new CtClass[0], newCtClass);
		newCtClass.addConstructor(newCtCons);
	}

	protected void addDefaultConstructor(CtClass newCtClass)
			throws CannotCompileException {
		CtConstructor newCtCons = CtNewConstructor
				.defaultConstructor(newCtClass);
		newCtClass.addConstructor(newCtCons);
	}

	protected void addTemplateArrayField(CtClass newCtClass)
			throws NotFoundException, CannotCompileException {
		CtClass acsCtClass = pool.get(TemplateAccessorImpl.class.getName());
		CtField tmplsField = acsCtClass
				.getDeclaredField(VARIABLE_NAME_TEMPLATES);
		CtField tmplsField2 = new CtField(tmplsField.getType(), tmplsField
				.getName(), newCtClass);
		newCtClass.addField(tmplsField2);
	}

	protected void addSetTemplatesMethod(CtClass newCtClass)
			throws NotFoundException, CannotCompileException {
		CtClass acsCtClass = pool.get(TemplateAccessorImpl.class.getName());
		CtMethod settmplsMethod = acsCtClass
				.getDeclaredMethod(METHOD_NAME_SETTEMPLATES);
		CtMethod settmplsMethod2 = CtNewMethod.copy(settmplsMethod, newCtClass,
				null);
		newCtClass.addMethod(settmplsMethod2);
	}

	protected Class<?> getPrimToWrapperType(Class<?> type) {
		if (type.equals(boolean.class)) {
			return Boolean.class;
		} else if (type.equals(byte.class)) {
			return Byte.class;
		} else if (type.equals(short.class)) {
			return Short.class;
		} else if (type.equals(int.class)) {
			return Integer.class;
		} else if (type.equals(long.class)) {
			return Long.class;
		} else if (type.equals(float.class)) {
			return Float.class;
		} else if (type.equals(double.class)) {
			return Double.class;
		} else {
			throw new MessageTypeException("Type error: " + type.getName());
		}
	}

	public static String getPrimTypeValueMethodName(Class<?> type) {
		if (type.equals(boolean.class)) {
			return METHOD_NAME_BOOLEANVALUE;
		} else if (type.equals(byte.class)) {
			return METHOD_NAME_BYTEVALUE;
		} else if (type.equals(short.class)) {
			return METHOD_NAME_SHORTVALUE;
		} else if (type.equals(int.class)) {
			return METHOD_NAME_INTVALUE;
		} else if (type.equals(long.class)) {
			return METHOD_NAME_LONGVALUE;
		} else if (type.equals(float.class)) {
			return METHOD_NAME_FLOATVALUE;
		} else if (type.equals(double.class)) {
			return METHOD_NAME_DOUBLEVALUE;
		} else {
			throw new MessageTypeException("Type error: " + type.getName());
		}
	}

	public static Template createTemplate(Type t) {
		if (t.getClass().equals(Class.class)) {
			Class<?> c = (Class<?>) t;
			if (c.equals(boolean.class) || c.equals(Boolean.class)) {
				return Templates.tBoolean();
			} else if (c.equals(byte.class) || c.equals(Byte.class)) {
				return Templates.tByte();
			} else if (c.equals(short.class) || c.equals(Short.class)) {
				return Templates.tShort();
			} else if (c.equals(int.class) || c.equals(Integer.class)) {
				return Templates.tInteger();
			} else if (c.equals(float.class) || c.equals(Float.class)) {
				return Templates.tFloat();
			} else if (c.equals(long.class) || c.equals(Long.class)) {
				return Templates.tLong();
			} else if (c.equals(double.class) || c.equals(Double.class)) {
				return Templates.tDouble();
			} else if (c.equals(String.class)) {
				return Templates.tString();
			} else if (c.equals(BigInteger.class)) {
				return Templates.tBigInteger();
			} else if (c.equals(ByteBuffer.class)) {
				return Templates.tByteBuffer();
			} else if (CustomConverter.isRegistered(c)) {// FIXME
				return (Template) CustomConverter.get(c);
			} else if (CustomMessage.isAnnotated(c, MessagePackMessage.class)) {
				// @MessagePackMessage
				Template tmpl = DynamicTemplate.create(c);
				CustomMessage.register(c, tmpl);
				return tmpl;
			} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
				// FIXME DelegatePacker
				UnsupportedOperationException e = new UnsupportedOperationException(
						"not supported yet. : " + c.getName());
				LOG.error(e.getMessage(), e);
				throw e;
			} else if (CustomMessage.isAnnotated(c, MessagePackOrdinalEnum.class)) {
				// @MessagePackOrdinalEnum
				Template tmpl = DynamicOrdinalEnumTemplate.create(c);
				CustomMessage.register(c, tmpl);
				return tmpl;
			} else if (MessagePackable.class.isAssignableFrom(c)
					|| MessageConvertable.class.isAssignableFrom(c)
					|| MessageUnpackable.class.isAssignableFrom(c)) {
				Template tmpl = new MessagePackUnpackConvertableTemplate(c);
				CustomMessage.register(c, tmpl);
				return tmpl;
			} else {
				throw new MessageTypeException("Type error: " + ((Class<?>) t).getName());
			}
		} else if (t instanceof GenericArrayType) {
			GenericArrayType gat = (GenericArrayType) t;
			Type gct = gat.getGenericComponentType();
			if (gct.equals(byte.class)) {
				return Templates.tByteArray();
			} else {
				throw new DynamicCodeGenException("Not supported yet: " + gat);
			}
		} else if (t instanceof ParameterizedType) {
			ParameterizedType pt = (ParameterizedType) t;
			Class<?> rawType = (Class<?>) pt.getRawType();
			if (rawType.equals(List.class)) {
				Type[] ats = pt.getActualTypeArguments();
				return Templates.tList(createTemplate(ats[0]));
			} else if (rawType.equals(Map.class)) {
				Type[] ats = pt.getActualTypeArguments();
				return Templates.tMap(createTemplate(ats[0]), createTemplate(ats[1]));
			} else if (rawType.equals(Collection.class)) {
				Type[] ats = pt.getActualTypeArguments();
				return Templates.tCollection(createTemplate(ats[0]));
			} else {
				throw new DynamicCodeGenException("Type error: "
						+ t.getClass().getName());
			}
		} else {
			throw new DynamicCodeGenException("Type error: "
					+ t.getClass().getName());
		}
	}

	static int getArrayDim(Class<?> type) {
		if (type.isArray()) {
			return 1 + getArrayDim(type.getComponentType());
		} else {
			return 0;
		}
	}

	static Class<?> getArrayBaseType(Class<?> type) {
		if (type.isArray()) {
			return getArrayBaseType(type.getComponentType());
		} else {
			return type;
		}
	}

	static String arrayTypeToString(Class<?> type) {
		StringBuilder sb = new StringBuilder();
		int dim = getArrayDim(type);
		Class<?> t = getArrayBaseType(type);
		sb.append(t.getName());
		for (int i = 0; i < dim; ++i) {
			sb.append(STRING_NAME_LEFT_RIGHT_SQUARE_BRACKET);
		}
		return sb.toString();
	}

	protected static String classToString(Class<?> type) {
		if (type.isArray()) {
			return arrayTypeToString(type);
		} else {
			return type.getName();
		}
	}

	protected CtClass classToCtClass(Class<?> type) throws NotFoundException {
		if (type.equals(void.class)) {
			return CtClass.voidType;
		} else if (type.isPrimitive()) {
			if (type.equals(boolean.class)) {
				return CtClass.booleanType;
			} else if (type.equals(byte.class)) {
				return CtClass.byteType;
			} else if (type.equals(char.class)) {
				return CtClass.charType;
			} else if (type.equals(short.class)) {
				return CtClass.shortType;
			} else if (type.equals(int.class)) {
				return CtClass.intType;
			} else if (type.equals(long.class)) {
				return CtClass.longType;
			} else if (type.equals(float.class)) {
				return CtClass.floatType;
			} else if (type.equals(double.class)) {
				return CtClass.doubleType;
			} else {
				throw new MessageTypeException("Fatal error: " + type.getName());
			}
		} else if (type.isArray()) {
			return pool.get(arrayTypeToString(type));
		} else {
			return pool.get(type.getName());
		}
	}

	protected static Class<?> createClass(CtClass newCtClass)
			throws CannotCompileException {
		return newCtClass.toClass(null, null);
	}
}
