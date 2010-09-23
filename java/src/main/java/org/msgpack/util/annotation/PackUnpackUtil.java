package org.msgpack.util.annotation;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.NotFoundException;

import org.msgpack.MessageConvertable;
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePackable;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class PackUnpackUtil {
	static class Constants {
		static final String POSTFIX_TYPE_NAME_ENHANCER = "_$$_Enhanced";

		static final String KEYWORD_MODIFIER_PUBLIC = "public";

		static final String KEYWORD_FOR = "for";

		static final String KEYWORD_THROWS = "throws";

		static final String KEYWORD_NEW = "new";

		static final String CHAR_NAME_SPACE = " ";

		static final String CHAR_NAME_COMMA = ",";

		static final String CHAR_NAME_EQUAL = "=";

		static final String CHAR_NAME_PLUS = "+";

		static final String CHAR_NAME_LESSTHAN = "<";

		static final String CHAR_NAME_RIGHT_PARENTHESIS = ")";

		static final String CHAR_NAME_LEFT_PARENTHESIS = "(";

		static final String CHAR_NAME_RIGHT_CURLY_BRACHET = "}";

		static final String CHAR_NAME_LEFT_CURLY_BRACHET = "{";

		static final String CHAR_NAME_RIGHT_SQUARE_BRACKET = "]";

		static final String CHAR_NAME_LEFT_SQUARE_BRACKET = "[";

		static final String CHAR_NAME_DOT = ".";

		static final String CHAR_NAME_SEMICOLON = ";";

		static final String VARIABLE_NAME_PK = "_$$_pk";

		static final String VARIABLE_NAME_SIZE = "_$$_len";

		static final String VARIABLE_NAME_ARRAY = "_$$_ary";

		static final String VARIABLE_NAME_LIST = "_$$_list";

		static final String VARIABLE_NAME_MAP = "_$$_map";

		static final String VARIABLE_NAME_KEY = "_$$_key";

		static final String VARIABLE_NAME_VAL = "_$$_val";

		static final String VARIABLE_NAME_ITER = "_$$_iter";

		static final String VARIABLE_NAME_MPO = "_$$_mpo";

		static final String VARIABLE_NAME_I = "i";

		static final String METHOD_NAME_VALUEOF = "valueOf";

		static final String METHOD_NAME_ADD = "add";

		static final String METHOD_NAME_PUT = "put";

		static final String METHOD_NAME_GET = "get";

		static final String METHOD_NAME_SIZE = "size";

		static final String METHOD_NAME_KEYSET = "keySet";

		static final String METHOD_NAME_ITERATOR = "iterator";

		static final String METHOD_NAME_HASNEXT = "hasNext";

		static final String METHOD_NAME_NEXT = "next";

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

		static final String METHOD_NAME_ASARRAY = "asArray";

		static final String METHOD_NAME_ASBOOLEAN = "asBoolean";

		static final String METHOD_NAME_ASBYTE = "asByte";

		static final String METHOD_NAME_ASSHORT = "asShort";

		static final String METHOD_NAME_ASINT = "asInt";

		static final String METHOD_NAME_ASFLOAT = "asFloat";

		static final String METHOD_NAME_ASLONG = "asLong";

		static final String METHOD_NAME_ASDOUBLE = "asDouble";

		static final String METHOD_NAME_ASSTRING = "asString";

		static final String METHOD_NAME_ASBYTEARRAY = "asByteArray";

		static final String METHOD_NAME_ASBIGINTEGER = "asBigInteger";
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
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass enhCtClass = pool.makeClass(enhName);
			setSuperclass(enhCtClass, origCtClass);
			setInterfaces(enhCtClass);
			addConstructor(enhCtClass);
			Field[] fields = getDeclaredFields(origClass);
			addMessagePackMethod(enhCtClass, fields);
			addMessageUnpackMethod(enhCtClass, fields);
			addMessageConvertMethod(enhCtClass, fields);
			return createClass(enhCtClass);
		}

		private void checkClassValidation(Class<?> origClass) {
			// not public, abstract, final
			int mod = origClass.getModifiers();
			if ((!(Modifier.isPublic(mod) || Modifier.isProtected(mod)))
					|| Modifier.isAbstract(mod) || Modifier.isFinal(mod)) {
				throwClassValidationException(origClass);
			}
			// interface, enum
			if (origClass.isInterface() || origClass.isEnum()) {
				throwClassValidationException(origClass);
			}
			// annotation
			checkPackUnpackAnnotation(origClass);
		}

		private static void throwClassValidationException(Class<?> origClass) {
			throw new PackUnpackUtilException(
					"it must be a public class and have @"
							+ MessagePackUnpackable.class.getName() + ": "
							+ origClass.getName());
		}

		private void checkPackUnpackAnnotation(Class<?> origClass) {
			Annotation anno = origClass
					.getAnnotation(MessagePackUnpackable.class);
			if (anno == null) {
				throwClassValidationException(origClass);
			}
		}

		private void checkDefaultConstructorValidation(Class<?> origClass) {
			Constructor<?> cons = null;
			try {
				cons = origClass.getDeclaredConstructor(new Class[0]);
			} catch (Exception e1) {
				throwConstructoValidationException(origClass);
			}

			int mod = cons.getModifiers();
			if (!(Modifier.isPublic(mod) || Modifier.isProtected(mod))) {
				throwConstructoValidationException(origClass);
			}
		}

		private static void throwConstructoValidationException(
				Class<?> origClass) {
			throw new PackUnpackUtilException(
					"it must have a public zero-argument constructor: "
							+ origClass.getName());
		}

		private void setSuperclass(CtClass enhCtClass, CtClass origCtClass)
				throws CannotCompileException {
			enhCtClass.setSuperclass(origCtClass);
		}

		private void setInterfaces(CtClass enhCtClass) throws NotFoundException {
			CtClass pacCtClass = pool.get(MessagePackable.class.getName());
			enhCtClass.addInterface(pacCtClass);
			CtClass unpacCtClass = pool.get(MessageUnpackable.class.getName());
			enhCtClass.addInterface(unpacCtClass);
			CtClass convCtClass = pool.get(MessageConvertable.class.getName());
			enhCtClass.addInterface(convCtClass);
		}

		private void addConstructor(CtClass enhCtClass)
				throws CannotCompileException {
			CtConstructor newCtCons = CtNewConstructor
					.defaultConstructor(enhCtClass);
			enhCtClass.addConstructor(newCtCons);
		}

		private Field[] getDeclaredFields(Class<?> origClass) {
			ArrayList<Field> allFields = new ArrayList<Field>();
			Class<?> nextClass = origClass;
			while (nextClass != Object.class) {
				Field[] fields = nextClass.getDeclaredFields();
				for (Field field : fields) {
					try {
						checkFieldValidation(field, allFields);
						allFields.add(field);
					} catch (PackUnpackUtilException e) { // ignore
					}
				}
				nextClass = nextClass.getSuperclass();
			}
			return allFields.toArray(new Field[0]);
		}

		private void checkFieldValidation(Field field, List<Field> fields) {
			// check modifiers (public or protected)
			int mod = field.getModifiers();
			if ((!(Modifier.isPublic(mod) || Modifier.isProtected(mod)))
					|| Modifier.isStatic(mod) || Modifier.isFinal(mod)
					|| Modifier.isTransient(mod) || field.isSynthetic()) {
				throwFieldValidationException(field);
			}
			// check same name
			for (Field f : fields) {
				if (f.getName().equals(field.getName())) {
					throwFieldValidationException(field);
				}
			}
		}

		private static void throwFieldValidationException(Field field) {
			throw new PackUnpackUtilException("it must be a public field: "
					+ field.getName());
		}

		private void addMessagePackMethod(CtClass enhCtClass, Field[] fields)
				throws CannotCompileException, NotFoundException {
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(void.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.METHOD_NAME_MSGPACK);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Packer.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_THROWS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(IOException.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_PACKARRAY);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(fields.length);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			for (Field field : fields) {
				insertCodeOfMessagePackCall(sb, field);
			}
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			// System.out.println("messagePack method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private void insertCodeOfMessagePackCall(StringBuilder sb, Field field) {
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_PACK);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void addMessageUnpackMethod(CtClass enhCtClass, Field[] fields)
				throws CannotCompileException, NotFoundException {
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(void.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.METHOD_NAME_MSGUNPACK);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Unpacker.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_THROWS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(MessageTypeException.class.getName());
			sb.append(Constants.CHAR_NAME_COMMA);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(IOException.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_UNPACKARRAY);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			insertCodeOfMessageUnpackCalls(sb, fields);
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			// System.out.println("messageUnpack method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private void insertCodeOfMessageUnpackCalls(StringBuilder sb,
				Field[] fields) throws NotFoundException {
			for (Field field : fields) {
				insertCodeOfMessageUnpackCall(sb, field, field.getType());
			}
		}

		private void insertCodeOfMessageUnpackCall(StringBuilder sb,
				Field field, Class<?> type) throws NotFoundException {
			if (type.isPrimitive()) {
				// primitive type
				insertCodeOfMessageUnpackCallForPrimitiveTypes(sb, field, type);
			} else if (type.equals(Boolean.class) || // Boolean
					type.equals(Byte.class) || // Byte
					type.equals(Double.class) || // Double
					type.equals(Float.class) || // Float
					type.equals(Integer.class) || // Integer
					type.equals(Long.class) || // Long
					type.equals(Short.class)) { // Short
				// reference type (wrapper type)
				insertCodeOfMessageUnpackCallForWrapperTypes(sb, field, type);
			} else if (type.equals(BigInteger.class) || // BigInteger
					type.equals(String.class) || // String
					type.equals(byte[].class)) { // byte[]
				// reference type (other type)
				insertCodeOfMessageUnpackCallForPrimitiveTypes(sb, field, type);
			} else if (List.class.isAssignableFrom(type)) {
				// List
				insertCodeOfMessageUnpackCallForListType(sb, field, type);
			} else if (Map.class.isAssignableFrom(type)) {
				// Map
				insertCodeOfMessageUnpackCallForMapType(sb, field, type);
			} else if (MessageUnpackable.class.isAssignableFrom(type)
					|| (getCache(type.getName()) != null)) {
				// MessageUnpackable
				insertCodeOfMessageUnpackCallForMsgUnpackableType(sb, field,
						type);
			} else {
				throw new NotFoundException("unknown type:  " + type.getName());
			}
		}

		private void insertCodeOfMessageUnpackCallForPrimitiveTypes(
				StringBuilder sb, Field field, Class<?> type)
				throws NotFoundException {
			// insert a right variable
			if (field != null) {
				sb.append(field.getName());
				sb.append(Constants.CHAR_NAME_SPACE);
				sb.append(Constants.CHAR_NAME_EQUAL);
				sb.append(Constants.CHAR_NAME_SPACE);
			}
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			// insert unpack method
			if (type.equals(boolean.class)) { // boolean
				sb.append(Constants.METHOD_NAME_UNPACKBOOLEAN);
			} else if (type.equals(byte.class)) { // byte
				sb.append(Constants.METHOD_NAME_UNPACKBYTE);
			} else if (type.equals(double.class)) { // double
				sb.append(Constants.METHOD_NAME_UNPACKDOUBLE);
			} else if (type.equals(float.class)) { // float
				sb.append(Constants.METHOD_NAME_UNPACKFLOAT);
			} else if (type.equals(int.class)) { // int
				sb.append(Constants.METHOD_NAME_UNPACKINT);
			} else if (type.equals(long.class)) { // long
				sb.append(Constants.METHOD_NAME_UNPACKLONG);
			} else if (type.equals(short.class)) { // short
				sb.append(Constants.METHOD_NAME_UNPACKSHORT);
			} else { // reference type
				if (type.equals(BigInteger.class)) { // BigInteger
					sb.append(Constants.METHOD_NAME_UNPACKBIGINTEGER);
				} else if (type.equals(String.class)) { // String
					sb.append(Constants.METHOD_NAME_UNPACKSTRING);
				} else if (type.equals(byte[].class)) { // byte[]
					sb.append(Constants.METHOD_NAME_UNPACKBYTEARRAY);
				} else {
					throw new NotFoundException("unknown type:  "
							+ type.getName());
				}
			}
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			if (field != null) {
				sb.append(Constants.CHAR_NAME_SEMICOLON);
				sb.append(Constants.CHAR_NAME_SPACE);
			}
		}

		private void insertCodeOfMessageUnpackCallForWrapperTypes(
				StringBuilder sb, Field field, Class<?> type)
				throws NotFoundException {
			// insert a right variable
			if (field != null) {
				sb.append(field.getName());
				sb.append(Constants.CHAR_NAME_SPACE);
				sb.append(Constants.CHAR_NAME_EQUAL);
				sb.append(Constants.CHAR_NAME_SPACE);
			}
			sb.append(type.getName());
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_VALUEOF);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			// insert the name of a unpack method
			if (type.equals(Boolean.class)) { // Boolean
				sb.append(Constants.METHOD_NAME_UNPACKBOOLEAN);
			} else if (type.equals(Byte.class)) { // Byte
				sb.append(Constants.METHOD_NAME_UNPACKBYTE);
			} else if (type.equals(Double.class)) { // Double
				sb.append(Constants.METHOD_NAME_UNPACKDOUBLE);
			} else if (type.equals(Float.class)) { // Float
				sb.append(Constants.METHOD_NAME_UNPACKFLOAT);
			} else if (type.equals(Integer.class)) { // Integer
				sb.append(Constants.METHOD_NAME_UNPACKINT);
			} else if (type.equals(Long.class)) { // Long
				sb.append(Constants.METHOD_NAME_UNPACKLONG);
			} else if (type.equals(Short.class)) { // Short
				sb.append(Constants.METHOD_NAME_UNPACKSHORT);
			} else {
				throw new NotFoundException("unknown type:  " + type.getName());
			}
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			if (field != null) {
				sb.append(Constants.CHAR_NAME_SEMICOLON);
				sb.append(Constants.CHAR_NAME_SPACE);
			}
		}

		private void insertCodeOfMessageUnpackCallForListType(StringBuilder sb,
				Field field, Class<?> type) throws NotFoundException {
			ParameterizedType generic = (ParameterizedType) field
					.getGenericType();
			Class<?> genericType = (Class<?>) generic.getActualTypeArguments()[0];

			// len
			sb.append(int.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_UNPACKARRAY);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// field initializer
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_NEW);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(ArrayList.class.getName());
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// for loop
			sb.append(Constants.KEYWORD_FOR);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(int.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(0);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LESSTHAN);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_PLUS);
			sb.append(Constants.CHAR_NAME_PLUS);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);

			// block
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_ADD);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			insertCodeOfMessageUnpackCall(sb, null, genericType);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void insertCodeOfMessageUnpackCallForMapType(StringBuilder sb,
				Field field, Class<?> type) throws NotFoundException {
			ParameterizedType generic = (ParameterizedType) field
					.getGenericType();
			Class<?> genericType0 = (Class<?>) generic.getActualTypeArguments()[0];
			Class<?> genericType1 = (Class<?>) generic.getActualTypeArguments()[1];

			// len
			sb.append(int.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_UNPACKMAP);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// field initializer
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_NEW);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(HashMap.class.getName());
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// for loop
			sb.append(Constants.KEYWORD_FOR);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(int.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(0);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LESSTHAN);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_PLUS);
			sb.append(Constants.CHAR_NAME_PLUS);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);

			// block map.
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_PUT);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			insertCodeOfMessageUnpackCall(sb, null, genericType0);
			sb.append(Constants.CHAR_NAME_COMMA);
			sb.append(Constants.CHAR_NAME_SPACE);
			insertCodeOfMessageUnpackCall(sb, null, genericType1);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void insertCodeOfMessageUnpackCallForMsgUnpackableType(
				StringBuilder sb, Field field, Class<?> type) {
			// insert a right variable // ignore
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_UNPACK);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(MessageUnpackable.class.getName());
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void addMessageConvertMethod(CtClass enhCtClass, Field[] fields)
				throws CannotCompileException {
			// messageConvert(MessagePackObject obj) throws MessageTypeException
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(void.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.METHOD_NAME_MSGCONVERT);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_MPO);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_THROWS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(MessageTypeException.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
			insertCodeOfMessagePackObjectArrayGet(sb);
			insertCodeOfMesageConvertCalls(sb, fields);
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			// System.out.println("messageConvert method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private void insertCodeOfMessagePackObjectArrayGet(StringBuilder sb) {
			// MessagePackObject[] ary = obj.asArray();
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(Constants.CHAR_NAME_RIGHT_SQUARE_BRACKET);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_ARRAY);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_MPO);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_ASARRAY);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void insertCodeOfMesageConvertCalls(StringBuilder sb,
				Field[] fields) {
			for (int i = 0; i < fields.length; ++i) {
				insertCodeOfMessageConvertCall(sb, fields[i], fields[i]
						.getType(), i, null);
			}
		}

		private void insertCodeOfMessageConvertCall(StringBuilder sb, Field f,
				Class<?> c, int i, String v) {
			if (c.isPrimitive()) { // primitive type
				insertCodeOfMessageConvertCallForPrimTypes(sb, f, c, i, v);
			} else { // reference type
				if (c.equals(Boolean.class) || c.equals(Byte.class)
						|| c.equals(Short.class) || c.equals(Integer.class)
						|| c.equals(Float.class) || c.equals(Long.class)
						|| c.equals(Double.class)) {
					// wrapper type
					insertCodeOfMessageConvertCallForWrapTypes(sb, f, c, i, v);
				} else if (c.equals(String.class) || c.equals(byte[].class)
						|| c.equals(BigInteger.class)) {
					insertCodeOfMessageConvertCallForPrimTypes(sb, f, c, i, v);
				} else if (List.class.isAssignableFrom(c)) {
					insertCodeOfMessageConvertCallForList(sb, f, c, i);
				} else if (Map.class.isAssignableFrom(c)) {
					insertCodeOfMessageConveretCallForMap(sb, f, c, i);
				} else if (MessageConvertable.class.isAssignableFrom(c)
						|| (getCache(c.getName()) != null)) {
					// TODO
					// TODO
					// TODO
					// ((MessageConvertable)f_i).messageConvert(ary[i]);
					sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
					sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
					sb.append(MessageConvertable.class.getName());
					sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
					sb.append(f.getName());
					sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
					sb.append(Constants.CHAR_NAME_DOT);
					sb.append(Constants.METHOD_NAME_MSGCONVERT);
					sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
					sb.append(Constants.VARIABLE_NAME_ARRAY);
					sb.append(Constants.CHAR_NAME_LEFT_SQUARE_BRACKET);
					sb.append(i);
					sb.append(Constants.CHAR_NAME_RIGHT_SQUARE_BRACKET);
					sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
					sb.append(Constants.CHAR_NAME_SEMICOLON);
					sb.append(Constants.CHAR_NAME_SPACE);
				} else {
					throw new MessageTypeException("Type error: " + c.getName());
				}
			}
		}

		private void insertCodeOfMessageConvertCallForPrimTypes(
				StringBuilder sb, Field f, Class<?> c, int i, String name) {
			// f0 = objs[0].intValue();
			if (f != null) {
				sb.append(f.getName());
				sb.append(Constants.CHAR_NAME_SPACE);
				sb.append(Constants.CHAR_NAME_EQUAL);
				sb.append(Constants.CHAR_NAME_SPACE);
				sb.append(Constants.VARIABLE_NAME_ARRAY);
				sb.append(Constants.CHAR_NAME_LEFT_SQUARE_BRACKET);
				sb.append(i);
				sb.append(Constants.CHAR_NAME_RIGHT_SQUARE_BRACKET);
			} else {
				sb.append(name);
			}
			sb.append(Constants.CHAR_NAME_DOT);
			if (c.equals(boolean.class)) {
				sb.append(Constants.METHOD_NAME_ASBOOLEAN);
			} else if (c.equals(byte.class)) {
				sb.append(Constants.METHOD_NAME_ASBYTE);
			} else if (c.equals(short.class)) {
				sb.append(Constants.METHOD_NAME_ASSHORT);
			} else if (c.equals(int.class)) {
				sb.append(Constants.METHOD_NAME_ASINT);
			} else if (c.equals(float.class)) {
				sb.append(Constants.METHOD_NAME_ASFLOAT);
			} else if (c.equals(long.class)) {
				sb.append(Constants.METHOD_NAME_ASLONG);
			} else if (c.equals(double.class)) {
				sb.append(Constants.METHOD_NAME_ASDOUBLE);
			} else if (c.equals(String.class)) {
				sb.append(Constants.METHOD_NAME_ASSTRING);
			} else if (c.equals(byte[].class)) {
				sb.append(Constants.METHOD_NAME_ASBYTEARRAY);
			} else if (c.equals(BigInteger.class)) {
				sb.append(Constants.METHOD_NAME_ASBIGINTEGER);
			} else {
				throw new MessageTypeException("Type error: " + c.getName());
			}
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			if (f != null) {
				sb.append(Constants.CHAR_NAME_SEMICOLON);
				sb.append(Constants.CHAR_NAME_SPACE);
			}
		}

		private void insertCodeOfMessageConvertCallForWrapTypes(
				StringBuilder sb, Field f, Class<?> c, int i, String v) {
			if (f != null) {
				sb.append(f.getName());
				sb.append(Constants.CHAR_NAME_SPACE);
				sb.append(Constants.CHAR_NAME_EQUAL);
				sb.append(Constants.CHAR_NAME_SPACE);
			}
			sb.append(Constants.KEYWORD_NEW);
			sb.append(Constants.CHAR_NAME_SPACE);
			if (c.equals(Boolean.class)) {
				sb.append(Boolean.class.getName());
			} else if (c.equals(Byte.class)) {
				sb.append(Byte.class.getName());
			} else if (c.equals(Short.class)) {
				sb.append(Short.class.getName());
			} else if (c.equals(Integer.class)) {
				sb.append(Integer.class.getName());
			} else if (c.equals(Float.class)) {
				sb.append(Float.class.getName());
			} else if (c.equals(Long.class)) {
				sb.append(Long.class.getName());
			} else if (c.equals(Double.class)) {
				sb.append(Double.class.getName());
			} else {
				throw new MessageTypeException("Type error: " + c.getName());
			}
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			if (f != null) {
				sb.append(Constants.VARIABLE_NAME_ARRAY);
				sb.append(Constants.CHAR_NAME_LEFT_SQUARE_BRACKET);
				sb.append(i);
				sb.append(Constants.CHAR_NAME_RIGHT_SQUARE_BRACKET);
			} else {
				sb.append(v);
			}
			sb.append(Constants.CHAR_NAME_DOT);
			if (c.equals(Boolean.class)) {
				sb.append(Constants.METHOD_NAME_ASBOOLEAN);
			} else if (c.equals(Byte.class)) {
				sb.append(Constants.METHOD_NAME_ASBYTE);
			} else if (c.equals(Short.class)) {
				sb.append(Constants.METHOD_NAME_ASSHORT);
			} else if (c.equals(Integer.class)) {
				sb.append(Constants.METHOD_NAME_ASINT);
			} else if (c.equals(Float.class)) {
				sb.append(Constants.METHOD_NAME_ASFLOAT);
			} else if (c.equals(Long.class)) {
				sb.append(Constants.METHOD_NAME_ASLONG);
			} else if (c.equals(Double.class)) {
				sb.append(Constants.METHOD_NAME_ASDOUBLE);
			} else {
				throw new MessageTypeException("Type error: " + c.getName());
			}
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			if (f != null) {
				sb.append(Constants.CHAR_NAME_SEMICOLON);
				sb.append(Constants.CHAR_NAME_SPACE);
			}
		}

		private void insertCodeOfMessageConvertCallForList(StringBuilder sb,
				Field field, Class<?> type, int i) {
			ParameterizedType generic = (ParameterizedType) field
					.getGenericType();
			Class<?> genericType = (Class<?>) generic.getActualTypeArguments()[0];

			// List<MessagePackObject> list = ary[i].asList();
			sb.append(List.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_LIST);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_ARRAY);
			sb.append(Constants.CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(i);
			sb.append(Constants.CHAR_NAME_RIGHT_SQUARE_BRACKET);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append("asList");
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// int size = list.size();
			sb.append(int.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_LIST);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// field initializer
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_NEW);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(ArrayList.class.getName());
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// for loop
			sb.append(Constants.KEYWORD_FOR);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(int.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(0);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LESSTHAN);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_PLUS);
			sb.append(Constants.CHAR_NAME_PLUS);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);

			// block begin
			sb.append(Constants.CHAR_NAME_LEFT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_VAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.VARIABLE_NAME_LIST);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_GET);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.VARIABLE_NAME_I);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_ADD);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			insertCodeOfMessageConvertCall(sb, null, genericType, -1,
					Constants.VARIABLE_NAME_VAL);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			// block end
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void insertCodeOfMessageConveretCallForMap(StringBuilder sb,
				Field f, Class<?> c, int i) {
			ParameterizedType generic = (ParameterizedType) f.getGenericType();
			Class<?> genericType0 = (Class<?>) generic.getActualTypeArguments()[0];
			Class<?> genericType1 = (Class<?>) generic.getActualTypeArguments()[1];

			// Map<MessagePackObject, MessagePackObject> map = ary[i].asMap();
			sb.append(Map.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_MAP);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_ARRAY);
			sb.append(Constants.CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(i);
			sb.append(Constants.CHAR_NAME_RIGHT_SQUARE_BRACKET);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append("asMap");
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// int size = list.size();
			sb.append(int.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_MAP);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_SIZE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// field initializer
			sb.append(f.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_NEW);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(HashMap.class.getName());
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			// for loop
			sb.append(Constants.KEYWORD_FOR);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Iterator.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_ITER);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_MAP);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_KEYSET);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_ITERATOR);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_ITER);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_HASNEXT);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);

			// block map.
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_KEY);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.VARIABLE_NAME_ITER);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_NEXT);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_VAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_EQUAL);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(MessagePackObject.class.getName());
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.VARIABLE_NAME_MAP);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_GET);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.VARIABLE_NAME_KEY);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			sb.append(f.getName());
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_PUT);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			insertCodeOfMessageConvertCall(sb, null, genericType0, -1,
					Constants.VARIABLE_NAME_KEY);
			sb.append(Constants.CHAR_NAME_COMMA);
			sb.append(Constants.CHAR_NAME_SPACE);
			insertCodeOfMessageConvertCall(sb, null, genericType1, -1,
					Constants.VARIABLE_NAME_VAL);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
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

	public static Object initEnhancedInstance(MessagePackObject obj,
			Class<?> origClass) {
		Object ret = newEnhancedInstance(origClass);
		((MessageConvertable) ret).messageConvert(obj);
		return ret;
	}

	public static Object initEnhancedInstance(MessagePackObject obj,
			Object origObj) {
		((MessageConvertable) origObj).messageConvert(obj);
		return origObj;
	}

	@MessagePackUnpackable
	public static class Image {
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

	public static void main(final String[] args) throws Exception {
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
		// System.out.println(src.equals(dst));
	}
}
