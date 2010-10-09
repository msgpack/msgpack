package org.msgpack.util.codegen;

import java.lang.reflect.Field;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.math.BigInteger;
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
import org.msgpack.MessageTypeException;
import org.msgpack.Template;
import org.msgpack.Templates;
import org.msgpack.annotation.MessagePackDelegate;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class DynamicCodeGenBase implements Constants {
	public static interface TemplateAccessor {
		void setTemplates(Template[] templates);
	}

	public static class TemplateAccessorImpl implements TemplateAccessor {
		public Template[] _$$_templates;

		public void setTemplates(Template[] _$$_tmpls) {
			_$$_templates = _$$_tmpls;
		}
	}

	private static Logger LOG = LoggerFactory
			.getLogger(DynamicCodeGenBase.class);

	private static AtomicInteger COUNTER = new AtomicInteger(0);

	protected static int inc() {
		return COUNTER.addAndGet(1);
	}

	protected ClassPool pool;

	public DynamicCodeGenBase() {
		pool = ClassPool.getDefault();
	}

	protected void checkTypeValidation(Class<?> type) {
		DynamicCodeGenException e = new DynamicCodeGenException("Fatal error: "
				+ type.getName());
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void throwTypeValidationException(Class<?> origClass,
			String message) throws DynamicCodeGenException {
		DynamicCodeGenException e = new DynamicCodeGenException(message + ": "
				+ origClass.getName());
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void checkDefaultConstructorValidation(Class<?> type) {
		DynamicCodeGenException e = new DynamicCodeGenException("Fatal error: "
				+ type.getName());
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void throwConstructorValidationException(Class<?> origClass) {
		DynamicCodeGenException e = new DynamicCodeGenException(
				"it must have a public zero-argument constructor: "
						+ origClass.getName());
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void throwFieldValidationException(Field f) {
		DynamicCodeGenException e = new DynamicCodeGenException(
				"it must be a public field: " + f.getName());
		LOG.debug(e.getMessage(), e);
		throw e;
	}

	protected static void throwMethodValidationException(Method method,
			String message) throws DynamicCodeGenException {
		DynamicCodeGenException e = new DynamicCodeGenException(message + ": "
				+ method.getName());
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected CtClass makeClass(String name) throws NotFoundException {
		DynamicCodeGenException e = new DynamicCodeGenException("Fatal error: "
				+ name);
		LOG.error(e.getMessage(), e);
		throw e;
	}

	protected void setInterface(CtClass packerCtClass, Class<?> infClass)
			throws NotFoundException {
		CtClass infCtClass = pool.get(infClass.getName());
		packerCtClass.addInterface(infCtClass);
	}

	protected void addDefaultConstructor(CtClass enhancedCtClass)
			throws CannotCompileException {
		CtConstructor newCtCons = CtNewConstructor
				.defaultConstructor(enhancedCtClass);
		enhancedCtClass.addConstructor(newCtCons);
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
			} else {
				throw new DynamicCodeGenException("Type error: "
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
			sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
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
