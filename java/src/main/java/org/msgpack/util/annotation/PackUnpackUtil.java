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

		static final String TYPE_NAME_VOID = void.class.getName();

		static final String TYPE_NAME_OBJECT = Object.class.getName();

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

		static final String CHAR_NAME_PLUS = "+";

		static final String CHAR_NAME_LESSTHAN = "<";

		static final String CHAR_NAME_RIGHT_PARENTHESIS = ")";

		static final String CHAR_NAME_LEFT_PARENTHESIS = "(";

		static final String CHAR_NAME_RIGHT_CURLY_BRACHET = "}";

		static final String CHAR_NAME_LEFT_CURLY_BRACHET = "{";

		static final String CHAR_NAME_DOT = ".";

		static final String CHAR_NAME_SEMICOLON = ";";

		static final String VARIABLE_NAME_PK = "pk";

		static final String VARIABLE_NAME_OBJ = "obj";

		static final String VARIABLE_NAME_SIZE = "len";

		static final String VARIABLE_NAME_I = "i";

		static final String METHOD_NAME_VALUEOF = "valueOf";

		static final String METHOD_NAME_ADD = "add";

		static final String METHOD_NAME_PUT = "put";

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
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass enhCtClass = pool.makeClass(enhName);
			setSuperclass(enhCtClass, origCtClass);
			setInterfaces(enhCtClass);
			addConstructor(enhCtClass);
			Field[] fields = getDeclaredFields(origClass);
			addMessagePackMethod(enhCtClass, origCtClass, fields);
			addMessageUnpackMethod(enhCtClass, origCtClass, fields);
			addMessageConvertMethod(enhCtClass, origCtClass, fields);
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

		private void addMessagePackMethod(CtClass enhCtClass,
				CtClass origCtClass, Field[] fields)
				throws CannotCompileException, NotFoundException {
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.TYPE_NAME_VOID);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.METHOD_NAME_MSGPACK);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.TYPE_NAME_PACKER);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_THROWS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.TYPE_NAME_IOEXCEPTION);
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
				insertCodeOfMessagePack(sb, field);
			}
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			//System.out.println("messagePack method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private void insertCodeOfMessagePack(StringBuilder sb, Field field) {
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_DOT);
			sb.append(Constants.METHOD_NAME_PACK);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(field.getName());
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void addMessageUnpackMethod(CtClass enhCtClass,
				CtClass origCtClass, Field[] fields)
				throws CannotCompileException, NotFoundException {
			StringBuilder sb = new StringBuilder();
			sb.append(Constants.KEYWORD_MODIFIER_PUBLIC);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.TYPE_NAME_VOID);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.METHOD_NAME_MSGUNPACK);
			sb.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(Constants.TYPE_NAME_UNPACKER);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.VARIABLE_NAME_PK);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.KEYWORD_THROWS);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.TYPE_NAME_MSGTYPEEXCEPTION);
			sb.append(Constants.CHAR_NAME_COMMA);
			sb.append(Constants.CHAR_NAME_SPACE);
			sb.append(Constants.TYPE_NAME_IOEXCEPTION);
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
			for (Field field : fields) {
				insertCodeOfMessageUnpack(sb, field, field.getType());
			}
			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			//System.out.println("messageUnpack method: " + sb.toString());
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhCtClass);
			enhCtClass.addMethod(newCtMethod);
		}

		private void insertCodeOfMessageUnpack(StringBuilder sb, Field field,
				Class<?> type) throws NotFoundException {
			if (type.isPrimitive()) {
				// primitive type
				insertCodeOfMessageUnpackForPrimitiveTypes(sb, field, type);
			} else if (type.equals(Boolean.class) || // Boolean
					type.equals(Byte.class) || // Byte
					type.equals(Double.class) || // Double
					type.equals(Float.class) || // Float
					type.equals(Integer.class) || // Integer
					type.equals(Long.class) || // Long
					type.equals(Short.class)) { // Short
				// reference type (wrapper type)
				insertCodeOfMessageUnpackForWrapperTypes(sb, field, type);
			} else if (type.equals(BigInteger.class) || // BigInteger
					type.equals(String.class) || // String
					type.equals(byte[].class)) { // byte[]
				// reference type (other type)
				insertCodeOfMessageUnpackForPrimitiveTypes(sb, field, type);
			} else if (List.class.isAssignableFrom(type)) {
				// List
				insertCodeOfMessageUnpackForListType(sb, field, type);
			} else if (Map.class.isAssignableFrom(type)) {
				// Map
				insertCodeOfMessageUnpackForMapType(sb, field, type);
			} else if (MessageUnpackable.class.isAssignableFrom(type)
					|| (getCache(type.getName()) != null)) {
				// MessageUnpackable
				insertCodeOfMessageUnpackForMsgUnpackableType(sb, field, type);
			} else {
				throw new NotFoundException("unknown type:  " + type.getName());
			}
		}

		private void insertCodeOfMessageUnpackForPrimitiveTypes(
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

		private void insertCodeOfMessageUnpackForWrapperTypes(StringBuilder sb,
				Field field, Class<?> type) throws NotFoundException {
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

		private void insertCodeOfMessageUnpackForListType(StringBuilder sb,
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
			insertCodeOfMessageUnpack(sb, null, genericType);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void insertCodeOfMessageUnpackForMapType(StringBuilder sb,
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
			insertCodeOfMessageUnpack(sb, null, genericType0);
			sb.append(Constants.CHAR_NAME_COMMA);
			sb.append(Constants.CHAR_NAME_SPACE);
			insertCodeOfMessageUnpack(sb, null, genericType1);
			sb.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(Constants.CHAR_NAME_SEMICOLON);
			sb.append(Constants.CHAR_NAME_SPACE);

			sb.append(Constants.CHAR_NAME_RIGHT_CURLY_BRACHET);
			sb.append(Constants.CHAR_NAME_SPACE);
		}

		private void insertCodeOfMessageUnpackForMsgUnpackableType(
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

		private void addMessageConvertMethod(CtClass enhCtClass,
				CtClass origCtClass, Field[] fields)
				throws CannotCompileException {
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
			//System.out.println("messageConvert method: " + sb.toString());
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
		//System.out.println(src.equals(dst));
	}
}
