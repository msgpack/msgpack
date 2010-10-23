package org.msgpack.util.codegen;

import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.math.BigInteger;
import java.util.Iterator;
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
import javassist.NotFoundException;

import org.msgpack.CustomConverter;
import org.msgpack.CustomMessage;
import org.msgpack.CustomPacker;
import org.msgpack.MessageConvertable;
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePackable;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Templates;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackDelegate;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.msgpack.packer.BigIntegerPacker;
import org.msgpack.packer.BooleanPacker;
import org.msgpack.packer.ByteArrayPacker;
import org.msgpack.packer.BytePacker;
import org.msgpack.packer.DoublePacker;
import org.msgpack.packer.FloatPacker;
import org.msgpack.packer.IntegerPacker;
import org.msgpack.packer.LongPacker;
import org.msgpack.packer.OptionalPacker;
import org.msgpack.packer.ShortPacker;
import org.msgpack.packer.StringPacker;
import org.msgpack.template.BigIntegerTemplate;
import org.msgpack.template.BooleanTemplate;
import org.msgpack.template.ByteArrayTemplate;
import org.msgpack.template.ByteTemplate;
import org.msgpack.template.ClassTemplate;
import org.msgpack.template.CollectionTemplate;
import org.msgpack.template.DoubleTemplate;
import org.msgpack.template.FloatTemplate;
import org.msgpack.template.IntegerTemplate;
import org.msgpack.template.ListTemplate;
import org.msgpack.template.LongTemplate;
import org.msgpack.template.MapTemplate;
import org.msgpack.template.OptionalTemplate;
import org.msgpack.template.ShortTemplate;
import org.msgpack.template.StringTemplate;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class DynamicCodeGenBase implements Constants {

	private static Logger LOG = LoggerFactory
			.getLogger(DynamicCodeGenBase.class);

	static class MessagePackablePacker implements MessagePacker {
		@SuppressWarnings("unused")
		private Class<?> type;

		MessagePackablePacker(Class<?> type) {
			this.type = type;
		}

		@Override
		public void pack(Packer packer, Object target) throws IOException {
			MessagePackable mp = MessagePackable.class.cast(target);
			mp.messagePack(packer);
		}
	}

	static class ListPacker implements MessagePacker {
		private MessagePacker elementPacker;

		ListPacker(MessagePacker elementPacker) {
			this.elementPacker = elementPacker;
		}

		@SuppressWarnings("unchecked")
		@Override
		public void pack(Packer packer, Object target) throws IOException {
			List<Object> list = (List<Object>) target;
			packer.packArray(list.size());
			for (Iterator<Object> iter = list.iterator(); iter.hasNext();) {
				elementPacker.pack(packer, iter.next());
			}
		}
	}

	static class MapPacker implements MessagePacker {
		private MessagePacker keyPacker;
		private MessagePacker valPacker;

		MapPacker(MessagePacker keyPacker, MessagePacker valPacker) {
			this.keyPacker = keyPacker;
			this.valPacker = valPacker;
		}

		@SuppressWarnings("unchecked")
		@Override
		public void pack(Packer packer, Object target) throws IOException {
			Map<Object, Object> map = (Map<Object, Object>) target;
			packer.packMap(map.size());
			for (Map.Entry<Object, Object> e : ((Map<Object, Object>) map)
					.entrySet()) {
				keyPacker.pack(packer, e.getKey());
				valPacker.pack(packer, e.getValue());
			}
		}

	}

	static class MessageUnpackableConvertableTemplate implements Template {
		private Class<?> type;

		MessageUnpackableConvertableTemplate(Class<?> type) {
			this.type = type;
		}

		@Override
		public Object unpack(Unpacker unpacker) throws IOException,
				MessageTypeException {
			try {
				MessageUnpackable obj = (MessageUnpackable) type.newInstance();
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
		public Object convert(MessagePackObject from)
				throws MessageTypeException {
			try {
				MessageConvertable obj = (MessageConvertable) type
						.newInstance();
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

	static interface MessagePackerAccessor {
		void setMessagePackers(MessagePacker[] packers);
	}

	static class MessagePackerAccessorImpl implements MessagePackerAccessor {
		public Class<?> type;

		public MessagePacker[] _$$_packers;

		public MessagePackerAccessorImpl() {
		}

		public MessagePackerAccessorImpl(Class<?> type) {
			this.type = type;
		}

		public void setMessagePackers(MessagePacker[] _$$_pks) {
			_$$_packers = _$$_pks;
		}
	}

	static interface TemplateAccessor {
		void setTemplates(Template[] templates);
	}

	static class TemplateAccessorImpl implements TemplateAccessor {
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

	public DynamicCodeGenBase() {
		pool = ClassPool.getDefault();
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

	protected void addMessagePackerArrayField(CtClass newCtClass)
			throws NotFoundException, CannotCompileException {
		CtClass acsCtClass = pool
				.get(MessagePackerAccessorImpl.class.getName());
		CtField pksField = acsCtClass.getDeclaredField(VARIABLE_NAME_PACKERS);
		CtField pksField2 = new CtField(pksField.getType(), pksField.getName(),
				newCtClass);
		newCtClass.addField(pksField2);
	}

	protected void addSetMessagePackersMethod(CtClass newCtClass)
			throws NotFoundException, CannotCompileException {
		CtClass acsCtClass = pool.get(TemplateAccessorImpl.class.getName());
		CtMethod setPksMethod = acsCtClass
				.getDeclaredMethod(METHOD_NAME_SETMESSAGEPACKERS);
		CtMethod setPksMethod2 = CtNewMethod.copy(setPksMethod, newCtClass,
				null);
		newCtClass.addMethod(setPksMethod2);
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

	public String getPrimTypeValueMethodName(Class<?> type) {
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

	public String getUnpackMethodName(Class<?> c)
			throws DynamicCodeGenException {
		if (c.equals(boolean.class) || c.equals(Boolean.class)) {
			return METHOD_NAME_UNPACKBOOLEAN;
		} else if (c.equals(byte.class) || c.equals(Byte.class)) {
			return METHOD_NAME_UNPACKBYTE;
		} else if (c.equals(short.class) || c.equals(Short.class)) {
			return METHOD_NAME_UNPACKSHORT;
		} else if (c.equals(int.class) || c.equals(Integer.class)) {
			return METHOD_NAME_UNPACKINT;
		} else if (c.equals(float.class) || c.equals(Float.class)) {
			return METHOD_NAME_UNPACKFLOAT;
		} else if (c.equals(long.class) || c.equals(Long.class)) {
			return METHOD_NAME_UNPACKLONG;
		} else if (c.equals(double.class) || c.equals(Double.class)) {
			return METHOD_NAME_UNPACKDOUBLE;
		} else if (c.equals(String.class)) {
			return METHOD_NAME_UNPACKSTRING;
		} else if (c.equals(byte[].class)) {
			return METHOD_NAME_UNPACKBYTEARRAY;
		} else if (c.equals(BigInteger.class)) {
			return METHOD_NAME_UNPACKBIGINTEGER;
		} else if (List.class.isAssignableFrom(c)) {
			return METHOD_NAME_UNPACK;
		} else if (Map.class.isAssignableFrom(c)) {
			return METHOD_NAME_UNPACK;
		} else {
			throw new DynamicCodeGenException("Type error: " + c.getName());
		}
	}

	public String getAsMethodName(Class<?> c) {
		if (c.equals(boolean.class) || c.equals(Boolean.class)) {
			return METHOD_NAME_ASBOOLEAN;
		} else if (c.equals(byte.class) || c.equals(Byte.class)) {
			return METHOD_NAME_ASBYTE;
		} else if (c.equals(short.class) || c.equals(Short.class)) {
			return METHOD_NAME_ASSHORT;
		} else if (c.equals(int.class) || c.equals(Integer.class)) {
			return METHOD_NAME_ASINT;
		} else if (c.equals(float.class) || c.equals(Float.class)) {
			return METHOD_NAME_ASFLOAT;
		} else if (c.equals(long.class) || c.equals(Long.class)) {
			return METHOD_NAME_ASLONG;
		} else if (c.equals(double.class) || c.equals(Double.class)) {
			return METHOD_NAME_ASDOUBLE;
		} else if (c.equals(String.class)) {
			return METHOD_NAME_ASSTRING;
		} else if (c.equals(byte[].class)) {
			return METHOD_NAME_ASBYTEARRAY;
		} else if (c.equals(BigInteger.class)) {
			return METHOD_NAME_ASBIGINTEGER;
		} else if (List.class.isAssignableFrom(c)) {
			return METHOD_NAME_ASLIST;
		} else if (Map.class.isAssignableFrom(c)) {
			return METHOD_NAME_ASMAP;
		} else {
			throw new DynamicCodeGenException("Type error: " + c.getName());
		}
	}

	public static MessagePacker toMessagePacker(Template tmpl) {
		if (tmpl instanceof BigIntegerTemplate) {
			return BigIntegerPacker.getInstance();
		} else if (tmpl instanceof BooleanTemplate) {
			return BooleanPacker.getInstance();
		} else if (tmpl instanceof ByteArrayTemplate) {
			return ByteArrayPacker.getInstance();
		} else if (tmpl instanceof ByteTemplate) {
			return BytePacker.getInstance();
		} else if (tmpl instanceof ClassTemplate) {
			UnsupportedOperationException e = new UnsupportedOperationException(
					"not supported yet.");
			LOG.error(e.getMessage(), e);
			throw e;
		} else if (tmpl instanceof CollectionTemplate) {
			UnsupportedOperationException e = new UnsupportedOperationException(
					"not supported yet.");
			LOG.error(e.getMessage(), e);
			throw e;
		} else if (tmpl instanceof DoubleTemplate) {
			return DoublePacker.getInstance();
		} else if (tmpl instanceof FloatTemplate) {
			return FloatPacker.getInstance();
		} else if (tmpl instanceof IntegerTemplate) {
			return IntegerPacker.getInstance();
		} else if (tmpl instanceof ListTemplate) {
			ListTemplate t = (ListTemplate) tmpl;
			return new ListPacker(toMessagePacker(t.getElementTemplate()));
		} else if (tmpl instanceof LongTemplate) {
			return LongPacker.getInstance();
		} else if (tmpl instanceof MapTemplate) {
			MapTemplate t = (MapTemplate) tmpl;
			return new MapPacker(toMessagePacker(t.getKeyTemplate()),
					toMessagePacker(t.getValueTemplate()));
		} else if (tmpl instanceof OptionalTemplate) {
			OptionalTemplate t = (OptionalTemplate) tmpl;
			return new OptionalPacker(toMessagePacker(t.getElementTemplate()));
		} else if (tmpl instanceof ShortTemplate) {
			return ShortPacker.getInstance();
		} else if (tmpl instanceof StringTemplate) {
			return StringPacker.getInstance();
		} else if (tmpl instanceof TemplateAccessorImpl) {
			Class<?> c = ((TemplateAccessorImpl) tmpl).type;
			if (CustomPacker.isRegistered(c)) {
				return CustomPacker.get(c);
			} else {
				MessagePacker packer = DynamicPacker.create(c);
				CustomMessage.registerPacker(c, packer);
				return packer;
			}
		}
		UnsupportedOperationException e = new UnsupportedOperationException(
				"not supported yet.");
		LOG.error(e.getMessage(), e);
		throw e;
	}

	public MessagePacker createMessagePacker(Type t) {
		if (t.getClass().equals(Class.class)) {
			Class<?> c = (Class<?>) t;
			if (c.equals(boolean.class) || c.equals(Boolean.class)) {
				return BooleanPacker.getInstance();
			} else if (c.equals(byte.class) || c.equals(Byte.class)) {
				return BytePacker.getInstance();
			} else if (c.equals(short.class) || c.equals(Short.class)) {
				return ShortPacker.getInstance();
			} else if (c.equals(int.class) || c.equals(Integer.class)) {
				return IntegerPacker.getInstance();
			} else if (c.equals(float.class) || c.equals(Float.class)) {
				return FloatPacker.getInstance();
			} else if (c.equals(long.class) || c.equals(Long.class)) {
				return LongPacker.getInstance();
			} else if (c.equals(double.class) || c.equals(Double.class)) {
				return DoublePacker.getInstance();
			} else if (c.equals(String.class)) {
				return StringPacker.getInstance();
			} else if (c.equals(BigInteger.class)) {
				return BigIntegerPacker.getInstance();
			} else if (CustomPacker.isRegistered(c)) {
				return CustomPacker.get(c);
			} else if (CustomMessage.isAnnotated(c, MessagePackMessage.class)) {
				// @MessagePackMessage
				MessagePacker packer = DynamicPacker.create(c);
				CustomMessage.registerPacker(c, packer);
				return packer;
			} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
				// FIXME DelegatePacker
				UnsupportedOperationException e = new UnsupportedOperationException(
						"not supported yet. : " + c.getName());
				LOG.error(e.getMessage(), e);
				throw e;
			} else if (CustomMessage.isAnnotated(c,
					MessagePackOrdinalEnum.class)) {
				// @MessagePackOrdinalEnum
				MessagePacker packer = DynamicOrdinalEnumPacker.create(c);
				CustomMessage.registerPacker(c, packer);
				return packer;
			} else if (MessagePackable.class.isAssignableFrom(c)) {
				MessagePacker packer = new MessagePackablePacker(c);
				CustomMessage.registerPacker(c, packer);
				return packer;
			} else {
				throw new MessageTypeException("Type error: "
						+ ((Class<?>) t).getName());
			}
		} else if (t instanceof GenericArrayType) {
			GenericArrayType gat = (GenericArrayType) t;
			Type gct = gat.getGenericComponentType();
			if (gct.equals(byte.class)) {
				return ByteArrayPacker.getInstance();
			} else {
				throw new DynamicCodeGenException("Not supported yet: " + gat);
			}
		} else if (t instanceof ParameterizedType) {
			ParameterizedType pt = (ParameterizedType) t;
			Class<?> rawType = (Class<?>) pt.getRawType();
			if (rawType.equals(List.class)) {
				Type[] ats = pt.getActualTypeArguments();
				return new ListPacker(createMessagePacker(ats[0]));
			} else if (rawType.equals(Map.class)) {
				Type[] ats = pt.getActualTypeArguments();
				return new MapPacker(createMessagePacker(ats[0]),
						createMessagePacker(ats[1]));
			} else {
				throw new DynamicCodeGenException("Type error: "
						+ t.getClass().getName());
			}
		} else {
			throw new DynamicCodeGenException("Type error: "
					+ t.getClass().getName());
		}
	}

	public Template createTemplate(Type t) {
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
			} else if (CustomConverter.isRegistered(c)) {
				return (Template) CustomConverter.get(c);
			} else if (CustomMessage.isAnnotated(c, MessagePackMessage.class)) {
				// @MessagePackMessage
				Template tmpl = DynamicTemplate.create(c);
				CustomMessage.registerTemplate(c, tmpl);
				return tmpl;
			} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
				// FIXME DelegatePacker
				UnsupportedOperationException e = new UnsupportedOperationException(
						"not supported yet. : " + c.getName());
				LOG.error(e.getMessage(), e);
				throw e;
			} else if (CustomMessage.isAnnotated(c,
					MessagePackOrdinalEnum.class)) {
				// @MessagePackOrdinalEnum
				Template tmpl = DynamicOrdinalEnumTemplate.create(c);
				CustomMessage.registerTemplate(c, tmpl);
				return tmpl;
			} else if (MessageConvertable.class.isAssignableFrom(c)
					|| MessageUnpackable.class.isAssignableFrom(c)) {
				Template tmpl = new MessageUnpackableConvertableTemplate(c);
				CustomMessage.registerTemplate(c, tmpl);
				return tmpl;
			} else {
				throw new MessageTypeException("Type error: "
						+ ((Class<?>) t).getName());
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
				return Templates.tMap(createTemplate(ats[0]),
						createTemplate(ats[1]));
			} else {
				throw new DynamicCodeGenException("Type error: "
						+ t.getClass().getName());
			}
		} else {
			throw new DynamicCodeGenException("Type error: "
					+ t.getClass().getName());
		}
	}

	protected int getArrayDim(Class<?> type) {
		if (type.isArray()) {
			return 1 + getArrayDim(type.getComponentType());
		} else {
			return 0;
		}
	}

	protected Class<?> getArrayBaseType(Class<?> type) {
		if (type.isArray()) {
			return getArrayBaseType(type.getComponentType());
		} else {
			return type;
		}
	}

	protected String arrayTypeToString(Class<?> type) {
		StringBuilder sb = new StringBuilder();
		int dim = getArrayDim(type);
		Class<?> t = getArrayBaseType(type);
		sb.append(t.getName());
		for (int i = 0; i < dim; ++i) {
			sb.append(STRING_NAME_LEFT_RIGHT_SQUARE_BRACKET);
		}
		return sb.toString();
	}

	protected String classToString(Class<?> type) {
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

	protected Class<?> createClass(CtClass newCtClass)
			throws CannotCompileException {
		return newCtClass.toClass(null, null);
	}
}
