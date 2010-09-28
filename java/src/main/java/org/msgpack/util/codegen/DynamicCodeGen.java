package org.msgpack.util.codegen;

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.NotFoundException;

import org.msgpack.MessagePackObject;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.MessageUnpacker;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

public class DynamicCodeGen extends DynamicCodeGenBase implements Constants {

	private static DynamicCodeGen INSTANCE;

	private static AtomicInteger COUNTER = new AtomicInteger(0);

	private static int inc() {
		return COUNTER.addAndGet(1);
	}

	public static DynamicCodeGen getInstance() {
		if (INSTANCE == null) {
			INSTANCE = new DynamicCodeGen();
		}
		return INSTANCE;
	}

	private ClassPool pool;

	private DynamicCodeGen() {
		this.pool = ClassPool.getDefault();
	}

	public Class<?> generateMessagePackerClass(Class<?> origClass) {
		try {
			String origName = origClass.getName();
			String packerName = origName + POSTFIX_TYPE_NAME_PACKER + inc();
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass packerCtClass = pool.makeClass(packerName);
			setInterface(packerCtClass, MessagePacker.class);
			addDefaultConstructor(packerCtClass);
			Field[] fields = getDeclaredFields(origClass);
			addPackMethod(packerCtClass, origClass, fields);
			return createClass(packerCtClass);
		} catch (NotFoundException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateMessageUnpackerClass(Class<?> origClass) {
		try {
			String origName = origClass.getName();
			String unpackerName = origName + POSTFIX_TYPE_NAME_UNPACKER + inc();
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass unpackerCtClass = pool.makeClass(unpackerName);
			setInterface(unpackerCtClass, MessageUnpacker.class);
			addDefaultConstructor(unpackerCtClass);
			Field[] fields = getDeclaredFields(origClass);
			addUnpackMethod(unpackerCtClass, origClass, fields);
			return createClass(unpackerCtClass);
		} catch (NotFoundException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateTemplateClass(Class<?> origClass) {
		try {
			String origName = origClass.getName();
			String tmplName = origName + POSTFIX_TYPE_NAME_TEMPLATE + inc();
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass tmplCtClass = pool.makeClass(tmplName);
			setInterface(tmplCtClass, Template.class);
			addDefaultConstructor(tmplCtClass);
			Field[] fields = getDeclaredFields(origClass);
			addUnpackMethod(tmplCtClass, origClass, fields);
			addConvertMethod(tmplCtClass, origClass, fields);
			return createClass(tmplCtClass);
		} catch (NotFoundException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	private void checkClassValidation(Class<?> origClass) {
		// not public, abstract, final
		int mod = origClass.getModifiers();
		if ((!(Modifier.isPublic(mod) || Modifier.isProtected(mod)))
				|| Modifier.isAbstract(mod) || Modifier.isFinal(mod)) {
			throwClassValidationException(origClass,
					"it must be a public class");
		}
		// interface, enum
		if (origClass.isInterface() || origClass.isEnum()) {
			throwClassValidationException(origClass,
					"it must not be an interface or enum");
		}
	}

	private static void throwClassValidationException(Class<?> origClass,
			String msg) {
		throw new DynamicCodeGenException(msg + ": " + origClass.getName());
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

	private static void throwConstructoValidationException(Class<?> origClass) {
		throw new DynamicCodeGenException(
				"it must have a public zero-argument constructor: "
						+ origClass.getName());
	}

	private void setInterface(CtClass packerCtClass, Class<?> infClass)
			throws NotFoundException {
		CtClass infCtClass = pool.get(infClass.getName());
		packerCtClass.addInterface(infCtClass);
	}

	private void addDefaultConstructor(CtClass enhCtClass)
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
				} catch (DynamicCodeGenException e) { // ignore
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
		throw new DynamicCodeGenException("it must be a public field: "
				+ field.getName());
	}

	private void addPackMethod(CtClass packerCtClass, Class<?> c, Field[] fs)
			throws CannotCompileException, NotFoundException {
		StringBuilder sb = new StringBuilder();
		StringBuilder bsb = new StringBuilder();
		insertPackMethodBody(bsb, c, fs);
		addPublicMethodDecl(sb, METHOD_NAME_PACK, void.class, new Class[] {
				Packer.class, Object.class }, new String[] { VARIABLE_NAME_PK,
				VARIABLE_NAME_OBJECT }, new Class[] { IOException.class }, bsb
				.toString());
		System.out.println("pack method: " + sb.toString());
		CtMethod newCtMethod = CtNewMethod.make(sb.toString(), packerCtClass);
		packerCtClass.addMethod(newCtMethod);
	}

	private void insertPackMethodBody(StringBuilder sb, Class<?> c, Field[] fs) {
		insertLocalVariableDecl(sb, c, VARIABLE_NAME_TARGET);
		StringBuilder mc = new StringBuilder();
		insertTypeCast(mc, c, VARIABLE_NAME_OBJECT);
		insertValueInsertion(sb, mc.toString());
		insertSemicolon(sb);
		insertMethodCall(sb, VARIABLE_NAME_PK, METHOD_NAME_PACKARRAY,
				new String[] { new Integer(fs.length).toString() });
		insertSemicolon(sb);
		for (Field f : fs) {
			insertCodeOfPackCall(sb, f);
		}
	}

	private void insertCodeOfPackCall(StringBuilder sb, Field field) {
		StringBuilder aname = new StringBuilder();
		aname.append(VARIABLE_NAME_TARGET);
		aname.append(CHAR_NAME_DOT);
		aname.append(field.getName());
		insertMethodCall(sb, VARIABLE_NAME_PK, METHOD_NAME_PACK,
				new String[] { aname.toString() });
		insertSemicolon(sb);
	}

	private void addUnpackMethod(CtClass unpackerCtClass, Class<?> c, Field[] fs)
			throws CannotCompileException, NotFoundException {
		// Object unpack(Unpacker pac) throws IOException, MessageTypeException;
		StringBuilder sb = new StringBuilder();
		StringBuilder bsb = new StringBuilder();
		insertUnpackMethodBody(bsb, c, fs);
		addPublicMethodDecl(sb, METHOD_NAME_UNPACK, Object.class,
				new Class<?>[] { Unpacker.class },
				new String[] { VARIABLE_NAME_PK }, new Class<?>[] {
						MessageTypeException.class, IOException.class }, bsb
						.toString());
		System.out.println("unpack method: " + sb.toString());
		CtMethod newCtMethod = CtNewMethod.make(sb.toString(), unpackerCtClass);
		unpackerCtClass.addMethod(newCtMethod);
	}

	private void insertUnpackMethodBody(StringBuilder sb, Class<?> c, Field[] fs) {
		insertLocalVariableDecl(sb, c, VARIABLE_NAME_TARGET);
		StringBuilder mc = new StringBuilder();
		insertDefaultConsCall(mc, c);
		insertValueInsertion(sb, mc.toString());
		insertSemicolon(sb);
		insertMethodCall(sb, VARIABLE_NAME_PK, METHOD_NAME_UNPACKARRAY,
				new String[0]);
		insertSemicolon(sb);
		for (Field f : fs) {
			insertCodeOfUnpackMethodCall(sb, f, f.getType());
		}
		insertReturnStat(sb, VARIABLE_NAME_TARGET);
		insertSemicolon(sb);
	}

	private void insertCodeOfUnpackMethodCall(StringBuilder sb, Field f,
			Class<?> c) {
		if (c.isPrimitive()) {
			// primitive type
			insertCodeOfUnpackMethodCallForPrimTypes(sb, f, c);
		} else if (c.equals(Boolean.class) || // Boolean
				c.equals(Byte.class) || // Byte
				c.equals(Double.class) || // Double
				c.equals(Float.class) || // Float
				c.equals(Integer.class) || // Integer
				c.equals(Long.class) || // Long
				c.equals(Short.class)) { // Short
			// reference type (wrapper type)
			insertCodeOfUnpackMethodCallForWrapTypes(sb, f, c);
		} else if (c.equals(BigInteger.class) || // BigInteger
				c.equals(String.class) || // String
				c.equals(byte[].class)) { // byte[]
			// reference type (other type)
			insertCodeOfUnpackMethodCallForPrimTypes(sb, f, c);
		} else if (List.class.isAssignableFrom(c)) {
			// List
			insertCodeOfUnpackMethodCallForListType(sb, f, c);
		} else if (Map.class.isAssignableFrom(c)) {
			// Map
			insertCodeOfUnpackMethodCallForMapType(sb, f, c);
		} else if (MessageUnpackable.class.isAssignableFrom(c)) {
			// MessageUnpackable
			insertCodeOfMessageUnpackCallForMsgUnpackableType(sb, f, c);
		} else {
			throw new MessageTypeException("unknown type:  " + c.getName());
		}
	}

	private void insertCodeOfUnpackMethodCallForPrimTypes(StringBuilder sb,
			Field f, Class<?> c) {
		if (f != null) {
			sb.append(VARIABLE_NAME_TARGET);
			sb.append(CHAR_NAME_DOT);
			sb.append(f.getName());
			sb.append(CHAR_NAME_SPACE);
			sb.append(CHAR_NAME_EQUAL);
			sb.append(CHAR_NAME_SPACE);
		}
		insertMethodCall(sb, VARIABLE_NAME_PK, getUnpackMethodName(c),
				new String[0]);
		if (f != null) {
			insertSemicolon(sb);
		}
	}

	private void insertCodeOfUnpackMethodCallForWrapTypes(StringBuilder sb,
			Field f, Class<?> c) {
		if (f != null) {
			sb.append(VARIABLE_NAME_TARGET);
			sb.append(f.getName());
			sb.append(CHAR_NAME_SPACE);
			sb.append(CHAR_NAME_EQUAL);
			sb.append(CHAR_NAME_SPACE);
		}
		StringBuilder mc = new StringBuilder();
		insertMethodCall(mc, VARIABLE_NAME_PK, getUnpackMethodName(c),
				new String[0]);
		insertMethodCall(sb, c.getName(), METHOD_NAME_VALUEOF,
				new String[] { mc.toString() });
		if (f != null) {
			sb.append(CHAR_NAME_SEMICOLON);
			sb.append(CHAR_NAME_SPACE);
		}
	}

	private void insertCodeOfUnpackMethodCallForListType(StringBuilder sb,
			Field field, Class<?> type) {
		ParameterizedType generic = (ParameterizedType) field.getGenericType();
		Class<?> genericType = (Class<?>) generic.getActualTypeArguments()[0];

		// len
		sb.append(int.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_SIZE);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_PK);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_UNPACKARRAY);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// field initializer
		sb.append(field.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(KEYWORD_NEW);
		sb.append(CHAR_NAME_SPACE);
		sb.append(ArrayList.class.getName());
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// for loop
		sb.append(KEYWORD_FOR);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(int.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_I);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(0);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_I);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LESSTHAN);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_SIZE);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_PLUS);
		sb.append(CHAR_NAME_PLUS);
		sb.append(VARIABLE_NAME_I);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);

		// block
		sb.append(field.getName());
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_ADD);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		insertCodeOfUnpackMethodCall(sb, null, genericType);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
	}

	private void insertCodeOfUnpackMethodCallForMapType(StringBuilder sb,
			Field field, Class<?> type) {
		ParameterizedType generic = (ParameterizedType) field.getGenericType();
		Class<?> genericType0 = (Class<?>) generic.getActualTypeArguments()[0];
		Class<?> genericType1 = (Class<?>) generic.getActualTypeArguments()[1];

		// len
		sb.append(int.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_SIZE);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_PK);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_UNPACKMAP);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// field initializer
		sb.append(field.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(KEYWORD_NEW);
		sb.append(CHAR_NAME_SPACE);
		sb.append(HashMap.class.getName());
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// for loop
		sb.append(KEYWORD_FOR);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(int.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_I);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(0);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_I);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LESSTHAN);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_SIZE);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_PLUS);
		sb.append(CHAR_NAME_PLUS);
		sb.append(VARIABLE_NAME_I);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);

		// block map.
		sb.append(field.getName());
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_PUT);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		insertCodeOfUnpackMethodCall(sb, null, genericType0);
		sb.append(CHAR_NAME_COMMA);
		sb.append(CHAR_NAME_SPACE);
		insertCodeOfUnpackMethodCall(sb, null, genericType1);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
	}

	// private void insertCodeOfMessageUnpackCallForEnhancedType(StringBuilder
	// sb,
	// Field f, Class<?> c) {
	// c = this.getCache(c.getName());
	// insertCodeOfMessageUnpackCallForMsgUnpackableType(sb, f, c);
	// }

	private void insertCodeOfMessageUnpackCallForMsgUnpackableType(
			StringBuilder sb, Field f, Class<?> c) {
		// if (fi == null) { fi = new Foo_$$_Enhanced(); }
		sb.append(KEYWORD_IF);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(f.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(KEYWORD_NULL);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		sb.append(f.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(KEYWORD_NEW);
		sb.append(CHAR_NAME_SPACE);
		sb.append(c.getName());
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);

		// insert a right variable // ignore
		sb.append(VARIABLE_NAME_PK);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_UNPACK);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(MessageUnpackable.class.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(f.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
	}

	private void addConvertMethod(CtClass tmplCtClass, Class<?> c, Field[] fs)
			throws CannotCompileException, NotFoundException {
		// Object convert(MessagePackObject from) throws MessageTypeException;
		// FIXME
	}

	private Class<?> createClass(CtClass packerCtClass)
			throws CannotCompileException {
		return packerCtClass.toClass(null, null);
	}
}
