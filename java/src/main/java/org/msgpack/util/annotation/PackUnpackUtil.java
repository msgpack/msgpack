package org.msgpack.util.annotation;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.lang.reflect.Modifier;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtField;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.NotFoundException;

import org.msgpack.MessageConvertable;
import org.msgpack.MessagePackable;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class PackUnpackUtil {
	static class Constants {
		static final String POSTFIX_TYPE_NAME_ENHANCER = "_$$_Enhanced";

		static final String KEYWORD_MODIFIER_PUBLIC = "public";

		static final String KEYWORD_THROWS = "throws";

		static final String TYPE_NAME_VOID = void.class.getName();

		static final String TYPE_NAME_BOOLEAN = boolean.class.getName();

		static final String TYPE_NAME_BYTE = byte.class.getName();

		static final String TYPE_NAME_DOUBLE = double.class.getName();

		static final String TYPE_NAME_FLOAT = float.class.getName();

		static final String TYPE_NAME_INT = int.class.getName();

		static final String TYPE_NAME_LONG = long.class.getName();

		static final String TYPE_NAME_SHORT = short.class.getName();

		static final String TYPE_NAME_OBJECT = Object.class.getName();

		static final String TYPE_NAME_BIGINTEGER = BigInteger.class.getName();

		static final String TYPE_NAME_STRING = String.class.getName();

		static final String TYPE_NAME_BOOLEAN2 = Boolean.class.getName();

		static final String TYPE_NAME_BYTE2 = Byte.class.getName();

		static final String TYPE_NAME_DOUBLE2 = Double.class.getName();

		static final String TYPE_NAME_FLOAT2 = Float.class.getName();

		static final String TYPE_NAME_INT2 = Integer.class.getName();

		static final String TYPE_NAME_LONG2 = Long.class.getName();

		static final String TYPE_NAME_SHORT2 = Short.class.getName();

		static final String TYPE_NAME_BYTEARRAY = byte[].class.getName();

		static final String TYPE_NAME_LIST = List.class.getName();

		static final String TYPE_NAME_MAP = Map.class.getName();

		static final String TYPE_NAME_IOEXCEPTION = IOException.class.getName();

		static final String TYPE_NAME_PACKER = Packer.class.getName();

		static final String TYPE_NAME_UNPACKER = Unpacker.class.getName();

		static final String TYPE_NAME_MSGPACKABLE = MessagePackable.class
				.getName();

		static final String TYPE_NAME_MSGUNPACKABLE = MessageUnpackable.class
				.getName();

		static final String TYPE_NAME_MSGCONVERTABLE = MessageConvertable.class
				.getName();

		static final String TYPE_NAME_MSGTYPEEXCEPTION = MessageTypeException.class
				.getName();

		static final String TYPE_NAME_MSGPACKUNPACKABLE = MessagePackUnpackable.class
				.getName();

		static final String TYPE_NAME_MSGPACKOPTIONAL = MessagePackOptional.class
				.getName();

		static final String TYPE_NAME_MSGPACKOREQUIRED = MessagePackRequired.class
				.getName();

		static final String CHAR_NAME_SPACE = " ";

		static final String CHAR_NAME_COMMA = ",";

		static final String CHAR_NAME_EQUAL = "=";

		static final String CHAR_NAME_RIGHT_PARENTHESIS = ")";

		static final String CHAR_NAME_LEFT_PARENTHESIS = "(";

		static final String CHAR_NAME_RIGHT_CURLY_BRACHET = "}";

		static final String CHAR_NAME_LEFT_CURLY_BRACHET = "{";

		static final String CHAR_NAME_DOT = ".";

		static final String CHAR_NAME_SEMICOLON = ";";

		static final String VARIABLE_NAME_PK = "pk";

		static final String VARIABLE_NAME_OBJ = "obj";

		static final String METHOD_NAME_VALUEOF = "valueOf";

		static final String METHOD_NAME_MSGPACK = "messagePack";

		static final String METHOD_NAME_MSGUNPACK = "messageUnpack";

		static final String METHOD_NAME_MSGCONVERT = "messageConvert";

		static final String METHOD_NAME_PACK = "pack";

		static final String METHOD_NAME_PACKARRAY = "packArray";

		static final String METHOD_NAME_UNPACK = "unpack";

		static final String METHOD_NAME_UNPACKBOOLEAN = "unpackBoolean";

		static final String METHOD_NAME_UNPACKBYTE = "unpackByte";

		static final String METHOD_NAME_UNPACKDOUBLE = "unpackDouble";

		static final String METHOD_NAME_UNPACKFLOAT = "unpackFloat";

		static final String METHOD_NAME_UNPACKINT = "unpackInt";

		static final String METHOD_NAME_UNPACKLONG = "unpackLong";

		static final String METHOD_NAME_UNPACKSHORT = "unpackShort";

		static final String METHOD_NAME_UNPACKSTRING = "unpackString";

		static final String METHOD_NAME_UNPACKBIGINTEGER = "unpackBigInteger";

		static final String METHOD_NAME_UNPACKOBJECT = "unpackObject";

		static final String METHOD_NAME_UNPACKBYTEARRAY = "unpackByteArray";

		static final String METHOD_NAME_UNPACKARRAY = "unpackArray";

		static final String METHOD_NAME_UNPACKMAP = "unpackMap";
	}

	public static class Enhancer {

		private ConcurrentHashMap<String, Class<?>> classCache;

		private ClassPool pool;

		protected Enhancer() {
			classCache = new ConcurrentHashMap<String, Class<?>>();
			pool = ClassPool.getDefault();
		}

		protected Class<?> getCache(String origName) {
			return classCache.get(origName);
		}

		protected void setCache(String origName, Class<?> enhClass) {
			classCache.putIfAbsent(origName, enhClass);
		}

		protected Class<?> generate(Class<?> origClass)
				throws NotFoundException, CannotCompileException {
			String origName = origClass.getName();
			String enhName = origName + Constants.POSTFIX_TYPE_NAME_ENHANCER;
			CtClass origCtClass = pool.get(origName);
			checkClassValidation(origCtClass);
			checkDefaultConstructorValidation(origCtClass);
			CtClass enhCtClass = pool.makeClass(enhName);
			setSuperclass(enhCtClass, origCtClass);
			setInterfaces(enhCtClass);
			addConstructor(enhCtClass);
			addMessagePackMethod(enhCtClass, origCtClass);
			addMessageUnpackMethod(enhCtClass, origCtClass);
			addMessageConvertMethod(enhCtClass, origCtClass);
			return createClass(enhCtClass);
		}

		private void checkClassValidation(CtClass origCtClass) {
			// not public, abstract, final
			int mod = origCtClass.getModifiers();
			if ((!Modifier.isPublic(mod)) || Modifier.isAbstract(mod)
					|| Modifier.isFinal(mod)) {
				throwClassValidationException(origCtClass);
			}
			// interface, enum
			if (origCtClass.isInterface() || origCtClass.isEnum()) {
				throwClassValidationException(origCtClass);
			}
			// annotation
			checkPackUnpackAnnotation(origCtClass);
		}

		private static void throwClassValidationException(CtClass origCtClass) {
			throw new PackUnpackUtilException(
					"it must be a public class and have @"
							+ MessagePackUnpackable.class.getName() + ": "
							+ origCtClass.getName());
		}

		private void checkPackUnpackAnnotation(CtClass origCtClass) {
			try {
				Object[] objs = origCtClass.getAnnotations();
				for (Object obj : objs) {
					if (obj instanceof MessagePackUnpackable) {
						return;
					}
				}
				throwClassValidationException(origCtClass);
			} catch (ClassNotFoundException e) {
				throw new PackUnpackUtilException(e.getMessage(), e);
			}
		}

		private void checkDefaultConstructorValidation(CtClass origCtClass) {
			CtConstructor cons = null;
			try {
				cons = origCtClass.getDeclaredConstructor(new CtClass[0]);
			} catch (NotFoundException e) {
				throwConstructoValidationException(origCtClass);
			}
			int mod = cons.getModifiers();
			if (!(Modifier.isPublic(mod) || Modifier.isProtected(mod))) {
				throwConstructoValidationException(origCtClass);
			}
		}

		private static void throwConstructoValidationException(
				CtClass origCtClass) {
			throw new PackUnpackUtilException(
					"it must have a public zero-argument constructor: "
							+ origCtClass.getName());
		}

		private void setSuperclass(CtClass enhCtClass, CtClass origCtClass)
				throws CannotCompileException {
			enhCtClass.setSuperclass(origCtClass);
		}

		private void setInterfaces(CtClass enhCtClass) throws NotFoundException {
			CtClass pacCtClass = pool.get(Constants.TYPE_NAME_MSGPACKABLE);
			enhCtClass.addInterface(pacCtClass);
			CtClass unpacCtClass = pool.get(Constants.TYPE_NAME_MSGUNPACKABLE);
			enhCtClass.addInterface(unpacCtClass);
			CtClass convCtClass = pool.get(Constants.TYPE_NAME_MSGCONVERTABLE);
			enhCtClass.addInterface(convCtClass);
		}

		private void addConstructor(CtClass enhCtClass)
				throws CannotCompileException {
			CtConstructor newCtCons = CtNewConstructor
					.defaultConstructor(enhCtClass);
			enhCtClass.addConstructor(newCtCons);
		}

		private void addMessagePackMethod(CtClass enhCtClass,
				CtClass origCtClass) throws CannotCompileException,
				NotFoundException {
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC).append(
					Constants.CHAR_NAME_SPACE).append(Constants.TYPE_NAME_VOID)
					.append(Constants.CHAR_NAME_SPACE).append(
							Constants.METHOD_NAME_MSGPACK).append(
							Constants.CHAR_NAME_LEFT_PARENTHESIS).append(
							Constants.TYPE_NAME_PACKER).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.VARIABLE_NAME_PK).append(
							Constants.CHAR_NAME_RIGHT_PARENTHESIS).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.KEYWORD_THROWS).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.TYPE_NAME_IOEXCEPTION).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.CHAR_NAME_LEFT_CURLY_BRACHET).append(
							Constants.CHAR_NAME_SPACE);
			CtField[] fields = origCtClass.getDeclaredFields();
			sb.append(Constants.VARIABLE_NAME_PK).append(
					Constants.CHAR_NAME_DOT).append(
					Constants.METHOD_NAME_PACKARRAY).append(
					Constants.CHAR_NAME_LEFT_PARENTHESIS).append(fields.length)
					.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS).append(
							Constants.CHAR_NAME_SEMICOLON).append(
							Constants.CHAR_NAME_SPACE);
			for (CtField field : fields) {
				insertCodeOfMessagePack(field, sb);
			}
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			System.out.println("messagePack method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private void insertCodeOfMessagePack(CtField field, StringBuilder sb)
				throws NotFoundException {
			sb.append(Constants.VARIABLE_NAME_PK).append(
					Constants.CHAR_NAME_DOT).append(Constants.METHOD_NAME_PACK)
					.append(Constants.CHAR_NAME_LEFT_PARENTHESIS).append(
							field.getName()).append(
							Constants.CHAR_NAME_RIGHT_PARENTHESIS).append(
							Constants.CHAR_NAME_SEMICOLON).append(
							Constants.CHAR_NAME_SPACE);
		}

		private void addMessageUnpackMethod(CtClass enhCtClass,
				CtClass origCtClass) throws CannotCompileException,
				NotFoundException {
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC).append(
					Constants.CHAR_NAME_SPACE).append(Constants.TYPE_NAME_VOID)
					.append(Constants.CHAR_NAME_SPACE).append(
							Constants.METHOD_NAME_MSGUNPACK).append(
							Constants.CHAR_NAME_LEFT_PARENTHESIS).append(
							Constants.TYPE_NAME_UNPACKER).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.VARIABLE_NAME_PK).append(
							Constants.CHAR_NAME_RIGHT_PARENTHESIS).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.KEYWORD_THROWS).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.TYPE_NAME_MSGTYPEEXCEPTION).append(
							Constants.CHAR_NAME_COMMA).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.TYPE_NAME_IOEXCEPTION).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.CHAR_NAME_LEFT_CURLY_BRACHET).append(
							Constants.CHAR_NAME_SPACE);
			CtField[] fields = origCtClass.getFields();
			sb.append(Constants.VARIABLE_NAME_PK).append(
					Constants.CHAR_NAME_DOT).append(
					Constants.METHOD_NAME_UNPACKARRAY).append(
					Constants.CHAR_NAME_LEFT_PARENTHESIS).append(
					Constants.CHAR_NAME_RIGHT_PARENTHESIS).append(
					Constants.CHAR_NAME_SEMICOLON).append(
					Constants.CHAR_NAME_SPACE);
			for (CtField field : fields) {
				insertCodeOfMessageUnpack(field, sb);
			}
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			System.out.println("messageUnpack method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private void insertCodeOfMessageUnpack(CtField field, StringBuilder sb)
				throws NotFoundException {
			CtClass type = field.getType();
			sb.append(field.getName()).append(Constants.CHAR_NAME_SPACE)
					.append(Constants.CHAR_NAME_EQUAL).append(
							Constants.CHAR_NAME_SPACE);
			insertValueOfMethodAndLeftParenthesis(sb, type);
			sb.append(Constants.VARIABLE_NAME_PK).append(
					Constants.CHAR_NAME_DOT);
			insertUnpackMethod(sb, type);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS).append(
					Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			insertValueOfMethodAndRightParenthesis(sb, type);
			sb.append(Constants.CHAR_NAME_SEMICOLON).append(
					Constants.CHAR_NAME_SPACE);

		}

		private void insertValueOfMethodAndLeftParenthesis(StringBuilder sb,
				CtClass type) throws NotFoundException {
			if (type.isPrimitive()) { // primitive type
				return;
			} else { // reference type
				if (type.equals(pool.get(Constants.TYPE_NAME_BOOLEAN2)) // Boolean
						|| type.equals(pool.get(Constants.TYPE_NAME_BYTE2)) // Byte
						|| type.equals(pool.get(Constants.TYPE_NAME_DOUBLE2)) // Double
						|| type.equals(pool.get(Constants.TYPE_NAME_FLOAT2)) // Float
						|| type.equals(pool.get(Constants.TYPE_NAME_INT2)) // Integer
						|| type.equals(pool.get(Constants.TYPE_NAME_LONG2)) // Long
						|| type.equals(pool.get(Constants.TYPE_NAME_SHORT2)) // Short
				) {
					sb.append(type.getName()).append(Constants.CHAR_NAME_DOT)
							.append(Constants.METHOD_NAME_VALUEOF).append(
									Constants.CHAR_NAME_LEFT_PARENTHESIS);
				} else {
					return;
				}
			}
		}

		private void insertUnpackMethod(StringBuilder sb, CtClass type)
				throws NotFoundException {
			if (type.equals(CtClass.booleanType)) { // boolean
				sb.append(Constants.METHOD_NAME_UNPACKBOOLEAN);
			} else if (type.equals(CtClass.byteType)) { // byte
				sb.append(Constants.METHOD_NAME_UNPACKBYTE);
			} else if (type.equals(CtClass.doubleType)) { // double
				sb.append(Constants.METHOD_NAME_UNPACKDOUBLE);
			} else if (type.equals(CtClass.floatType)) { // float
				sb.append(Constants.METHOD_NAME_UNPACKFLOAT);
			} else if (type.equals(CtClass.intType)) { // int
				sb.append(Constants.METHOD_NAME_UNPACKINT);
			} else if (type.equals(CtClass.longType)) { // long
				sb.append(Constants.METHOD_NAME_UNPACKLONG);
			} else if (type.equals(CtClass.shortType)) { // short
				sb.append(Constants.METHOD_NAME_UNPACKSHORT);
			} else { // reference type
				if (type.equals(pool.get(Constants.TYPE_NAME_BOOLEAN2))) { // Boolean
					sb.append(Constants.METHOD_NAME_UNPACKBOOLEAN);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_BYTE2))) { // Byte
					sb.append(Constants.METHOD_NAME_UNPACKBYTE);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_DOUBLE2))) { // Double
					sb.append(Constants.METHOD_NAME_UNPACKDOUBLE);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_FLOAT2))) { // Float
					sb.append(Constants.METHOD_NAME_UNPACKFLOAT);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_INT2))) { // Integer
					sb.append(Constants.METHOD_NAME_UNPACKINT);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_LONG2))) { // Long
					sb.append(Constants.METHOD_NAME_UNPACKLONG);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_SHORT2))) { // Short
					sb.append(Constants.METHOD_NAME_UNPACKSHORT);
				} else if (type
						.equals(pool.get(Constants.TYPE_NAME_BIGINTEGER))) { // BigInteger
					sb.append(Constants.METHOD_NAME_UNPACKBIGINTEGER);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_STRING))) { // String
					sb.append(Constants.METHOD_NAME_UNPACKSTRING);
				} else if (type.equals(pool.get(Constants.TYPE_NAME_BYTEARRAY))) { // byte[]
					sb.append(Constants.METHOD_NAME_UNPACKBYTEARRAY);
				} else if (type.subtypeOf(pool.get(Constants.TYPE_NAME_LIST))) { // List
					sb.append(Constants.METHOD_NAME_UNPACKARRAY);
				} else if (type.subtypeOf(pool.get(Constants.TYPE_NAME_MAP))) { // Map
					sb.append(Constants.METHOD_NAME_UNPACKMAP);
				} else if (type.subtypeOf(pool
						.get(Constants.TYPE_NAME_MSGUNPACKABLE))) { // MessageUnpackable
					sb.append(Constants.METHOD_NAME_UNPACKOBJECT);
				} else {
					throw new NotFoundException("unknown type:  "
							+ type.getName());
				}
			}
		}

		private void insertValueOfMethodAndRightParenthesis(StringBuilder sb,
				CtClass type) throws NotFoundException {
			if (type.isPrimitive()) { // primitive type
				return;
			} else { // reference type
				if (type.equals(pool.get(Constants.TYPE_NAME_BOOLEAN2)) // Boolean
						|| type.equals(pool.get(Constants.TYPE_NAME_BYTE2)) // Byte
						|| type.equals(pool.get(Constants.TYPE_NAME_DOUBLE2)) // Double
						|| type.equals(pool.get(Constants.TYPE_NAME_FLOAT2)) // Float
						|| type.equals(pool.get(Constants.TYPE_NAME_INT2)) // Integer
						|| type.equals(pool.get(Constants.TYPE_NAME_LONG2)) // Long
						|| type.equals(pool.get(Constants.TYPE_NAME_SHORT2)) // Short
				) {
					sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
				} else {
					return;
				}
			}
		}

		private void addMessageConvertMethod(CtClass enhCtClass,
				CtClass origCtClass) throws CannotCompileException {
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC).append(
					Constants.CHAR_NAME_SPACE).append(Constants.TYPE_NAME_VOID)
					.append(Constants.CHAR_NAME_SPACE).append(
							Constants.METHOD_NAME_MSGCONVERT).append(
							Constants.CHAR_NAME_LEFT_PARENTHESIS).append(
							Constants.TYPE_NAME_OBJECT).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.VARIABLE_NAME_OBJ).append(
							Constants.CHAR_NAME_RIGHT_PARENTHESIS).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.KEYWORD_THROWS).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.TYPE_NAME_MSGTYPEEXCEPTION).append(
							Constants.CHAR_NAME_SPACE).append(
							Constants.CHAR_NAME_LEFT_CURLY_BRACHET).append(
							Constants.CHAR_NAME_SPACE);
			// TODO
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			System.out.println("messageConvert method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private Class<?> createClass(CtClass enhCtClass)
				throws CannotCompileException {
			return enhCtClass.toClass(null, null);
		}
	}

	private static Enhancer enhancer;

	public static Class<?> getEnhancedClass(Class<?> origClass) {
		if (enhancer == null) {
			enhancer = new Enhancer();
		}

		String origName = origClass.getName();
		Class<?> enhClass = enhancer.getCache(origName);
		if (enhClass == null) {
			// generate a class object related to the original class
			try {
				enhClass = enhancer.generate(origClass);
			} catch (NotFoundException e) {
				throw new PackUnpackUtilException(e.getMessage(), e);
			} catch (CannotCompileException e) {
				throw new PackUnpackUtilException(e.getMessage(), e);
			}
			// set the generated class to the cache
			enhancer.setCache(origName, enhClass);
		}
		return enhClass;
	}

	public static Object newEnhancedInstance(Class<?> origClass) {
		try {
			Class<?> enhClass = getEnhancedClass(origClass);
			// create a new object of the generated class
			return enhClass.newInstance();
		} catch (InstantiationException e) {
			throw new PackUnpackUtilException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new PackUnpackUtilException(e.getMessage(), e);
		}
	}

	public static void main(final String[] args) throws Exception {
		@MessagePackUnpackable
		class Image {
			public String uri = "";

			public String title = "";

			public int width = 0;

			public int height = 0;

			public int size = 0;

			public boolean equals(Image obj) {
				return uri.equals(obj.uri) && title.equals(obj.title)
						&& width == obj.width && height == obj.height
						&& size == obj.size;
			}

			public boolean equals(Object obj) {
				if (obj.getClass() != Image.class) {
					return false;
				}
				return equals((Image) obj);
			}
		}

		PackUnpackUtil.getEnhancedClass(Image.class);
		Image src = (Image) PackUnpackUtil.newEnhancedInstance(Image.class);
		src.title = "msgpack";
		src.uri = "http://msgpack.org/";
		src.width = 2560;
		src.height = 1600;
		src.size = 4096000;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		Image dst = (Image) PackUnpackUtil.newEnhancedInstance(Image.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
		System.out.println(src.equals(dst));
	}
}
