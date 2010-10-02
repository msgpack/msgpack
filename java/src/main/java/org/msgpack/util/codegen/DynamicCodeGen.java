package org.msgpack.util.codegen;

import java.io.IOException;
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
import java.util.concurrent.atomic.AtomicInteger;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.NotFoundException;

import org.msgpack.CustomConverter;
import org.msgpack.CustomMessage;
import org.msgpack.CustomPacker;
import org.msgpack.CustomUnpacker;
import org.msgpack.MessageConvertable;
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePackable;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.MessageUnpacker;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackDelegate;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class DynamicCodeGen extends DynamicCodeGenBase implements Constants {

	private static Logger LOG = LoggerFactory.getLogger(DynamicCodeGen.class);

	private static DynamicCodeGen INSTANCE;

	private static AtomicInteger COUNTER = new AtomicInteger(0);

	private static int inc() {
		return COUNTER.addAndGet(1);
	}

	public static DynamicCodeGen getInstance() {
		if (INSTANCE == null) {
			LOG.info("create an instance of the type: "
					+ DynamicCodeGen.class.getName());
			INSTANCE = new DynamicCodeGen();
		}
		return INSTANCE;
	}

	private ClassPool pool;

	private DynamicCodeGen() {
		this.pool = ClassPool.getDefault();
	}

	public Class<?> generateMessagePackerClass(Class<?> origClass) {
		LOG.debug("start generating a MessagePacker impl.: "
				+ origClass.getName());
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
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateOrdinalEnumPackerClass(Class<?> origClass) {
		LOG.debug("start generating a OrdinalEnumPacker impl.: "
				+ origClass.getName());
		try {
			String origName = origClass.getName();
			String packerName = origName + POSTFIX_TYPE_NAME_PACKER + inc();
			checkClassValidation(origClass);
			CtClass packerCtClass = pool.makeClass(packerName);
			setInterface(packerCtClass, MessagePacker.class);
			addDefaultConstructor(packerCtClass);
			addPackMethodForOrdinalEnumTypes(packerCtClass, origClass);
			return createClass(packerCtClass);
		} catch (NotFoundException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateMessageUnpackerClass(Class<?> origClass) {
		LOG.debug("start generating a MessageUnpacker impl.: "
				+ origClass.getName());
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
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateOrdinalEnumUnpackerClass(Class<?> origClass) {
		LOG.debug("start generating a OrdinalEnumUnpacker impl.: "
				+ origClass.getName());
		try {
			String origName = origClass.getName();
			String unpackerName = origName + POSTFIX_TYPE_NAME_UNPACKER + inc();
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass unpackerCtClass = pool.makeClass(unpackerName);
			setInterface(unpackerCtClass, MessageUnpacker.class);
			addDefaultConstructor(unpackerCtClass);
			addUnpackMethodForOrdinalEnumTypes(unpackerCtClass, origClass);
			return createClass(unpackerCtClass);
		} catch (NotFoundException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateMessageConverterClass(Class<?> origClass) {
		LOG.debug("start generating a MessageConverter impl.: "
				+ origClass.getName());
		try {
			String origName = origClass.getName();
			String convName = origName + POSTFIX_TYPE_NAME_CONVERTER + inc();
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass converterCtClass = pool.makeClass(convName);
			setInterface(converterCtClass, MessageUnpacker.class);
			addDefaultConstructor(converterCtClass);
			Field[] fields = getDeclaredFields(origClass);
			addConvertMethod(converterCtClass, origClass, fields);
			return createClass(converterCtClass);
		} catch (NotFoundException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateOrdinalEnumConverterClass(Class<?> origClass) {
		LOG.debug("start generating a OrdinalEnumConverter impl.: "
				+ origClass.getName());
		try {
			String origName = origClass.getName();
			String convName = origName + POSTFIX_TYPE_NAME_CONVERTER + inc();
			checkClassValidation(origClass);
			CtClass converterCtClass = pool.makeClass(convName);
			setInterface(converterCtClass, MessageUnpacker.class);
			addDefaultConstructor(converterCtClass);
			addConvertMethodForOrdinalEnumTypes(converterCtClass, origClass);
			return createClass(converterCtClass);
		} catch (NotFoundException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateTemplateClass(Class<?> origClass) {
		LOG.debug("start generating a Template impl.: " + origClass.getName());
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
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateOrdinalEnumTemplateClass(Class<?> origClass) {
		LOG.debug("start generating a OrdinalEnumTemplate impl.: "
				+ origClass.getName());
		try {
			String origName = origClass.getName();
			String tmplName = origName + POSTFIX_TYPE_NAME_TEMPLATE + inc();
			checkClassValidation(origClass);
			CtClass tmplCtClass = pool.makeClass(tmplName);
			setInterface(tmplCtClass, Template.class);
			addDefaultConstructor(tmplCtClass);
			addUnpackMethodForOrdinalEnumTypes(tmplCtClass, origClass);
			addConvertMethodForOrdinalEnumTypes(tmplCtClass, origClass);
			return createClass(tmplCtClass);
		} catch (NotFoundException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	private void checkClassValidation(Class<?> origClass) {
		// not public, abstract
		int mod = origClass.getModifiers();
		if ((!Modifier.isPublic(mod)) || Modifier.isAbstract(mod)) {
			throwClassValidationException(origClass,
					"a class must have a public modifier");
		}
		// interface
		if (origClass.isInterface()) {
			throwClassValidationException(origClass,
					"cannot generate packer and unpacker for an interface");
		}
	}

	private static void throwClassValidationException(Class<?> origClass,
			String msg) {
		DynamicCodeGenException e = new DynamicCodeGenException(msg + ": "
				+ origClass.getName());
		LOG.error(e.getMessage(), e);
		throw e;
	}

	private void checkDefaultConstructorValidation(Class<?> origClass) {
		Constructor<?> cons = null;
		try {
			cons = origClass.getDeclaredConstructor(new Class[0]);
		} catch (Exception e1) {
			throwConstructorValidationException(origClass);
		}
		int mod = cons.getModifiers();
		if (!Modifier.isPublic(mod)) {
			throwConstructorValidationException(origClass);
		}
	}

	private static void throwConstructorValidationException(Class<?> origClass) {
		DynamicCodeGenException e = new DynamicCodeGenException(
				"it must have a public zero-argument constructor: "
						+ origClass.getName());
		LOG.error(e.getMessage(), e);
		throw e;
	}

	private void setInterface(CtClass packerCtClass, Class<?> infClass)
			throws NotFoundException {
		CtClass infCtClass = pool.get(infClass.getName());
		packerCtClass.addInterface(infCtClass);
	}

	private void addDefaultConstructor(CtClass dstCtClass)
			throws CannotCompileException {
		CtConstructor newCtCons = CtNewConstructor
				.defaultConstructor(dstCtClass);
		dstCtClass.addConstructor(newCtCons);
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

	private void checkFieldValidation(Field f, List<Field> fs) {
		// check that it has a public modifier
		int mod = f.getModifiers();
		if ((!(Modifier.isPublic(mod))) || Modifier.isStatic(mod)
				|| Modifier.isFinal(mod) || Modifier.isTransient(mod)
				|| f.isSynthetic()) {
			throwFieldValidationException(f);
		}
		// check same name
		for (Field f0 : fs) {
			if (f0.getName().equals(f.getName())) {
				throwFieldValidationException(f);
			}
		}
	}

	private static void throwFieldValidationException(Field f) {
		DynamicCodeGenException e = new DynamicCodeGenException(
				"it must be a public field: " + f.getName());
		LOG.debug(e.getMessage(), e);
		throw e;
	}

	private void addPackMethod(CtClass packerCtClass, Class<?> c, Field[] fs) {
		// void pack(Packer pk, Object target) throws IOException;
		StringBuilder sb = new StringBuilder();
		StringBuilder bsb = new StringBuilder();
		insertPackMethodBody(bsb, c, fs);
		addPublicMethodDecl(sb, METHOD_NAME_PACK, void.class, new Class[] {
				Packer.class, Object.class }, new String[] { VARIABLE_NAME_PK,
				VARIABLE_NAME_OBJECT }, new Class[] { IOException.class }, bsb
				.toString());
		LOG.trace("pack method src: " + sb.toString());
		try {
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(),
					packerCtClass);
			packerCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
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
			insertCodeOfPackMethodCall(sb, f);
		}
	}

	private void insertCodeOfPackMethodCall(StringBuilder sb, Field field) {
		Class<?> c = field.getType();
		if (c.isPrimitive()) {
		} else if (c.equals(Boolean.class) || c.equals(Byte.class)
				|| c.equals(Double.class) || c.equals(Float.class)
				|| c.equals(Integer.class) || c.equals(Long.class)
				|| c.equals(Short.class)) {
			; // ignore
		} else if (c.equals(String.class) || c.equals(BigInteger.class)
				|| c.equals(byte[].class)) {
			; // ignore
		} else if (List.class.isAssignableFrom(c)
				|| Map.class.isAssignableFrom(c)) {
			; // ignore
		} else if (CustomPacker.isRegistered(c)) {
			; // ignore
		} else if (MessagePackable.class.isAssignableFrom(c)) {
			; // ignore
		} else if (CustomMessage.isAnnotated(c, MessagePackMessage.class)) {
			// @MessagePackMessage
			MessagePacker packer = DynamicCodeGenPacker.create(c);
			CustomMessage.registerPacker(c, packer);
		} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
			// FIXME DelegatePacker
			UnsupportedOperationException e = new UnsupportedOperationException(
					"not supported yet. : " + c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		} else if (CustomMessage.isAnnotated(c, MessagePackOrdinalEnum.class)) {
			// @MessagePackOrdinalEnum
			MessagePacker packer = DynamicCodeGenOrdinalEnumPacker.create(c);
			CustomMessage.registerPacker(c, packer);
		} else {
			MessageTypeException e = new MessageTypeException("unknown type: "
					+ c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		}
		StringBuilder fa = new StringBuilder();
		insertFieldAccess(fa, VARIABLE_NAME_TARGET, field.getName());
		insertMethodCall(sb, VARIABLE_NAME_PK, METHOD_NAME_PACK,
				new String[] { fa.toString() });
		insertSemicolon(sb);
	}

	private void addPackMethodForOrdinalEnumTypes(CtClass packerCtClass,
			Class<?> c) throws CannotCompileException, NotFoundException {
		// void pack(Packer pk, Object target) throws IOException;
		StringBuilder sb = new StringBuilder();
		StringBuilder bsb = new StringBuilder();
		insertLocalVariableDecl(bsb, c, VARIABLE_NAME_TARGET);
		StringBuilder fa = new StringBuilder();
		insertTypeCast(fa, c, VARIABLE_NAME_OBJECT);
		insertValueInsertion(bsb, fa.toString());
		insertSemicolon(bsb);
		insertMethodCall(bsb, VARIABLE_NAME_PK, METHOD_NAME_PACKARRAY,
				new String[] { new Integer(1).toString() });
		insertSemicolon(bsb);
		fa = new StringBuilder();
		insertTypeCast(fa, Enum.class, VARIABLE_NAME_TARGET);
		String t = fa.toString();
		fa = new StringBuilder();
		insertMethodCall(fa, t, METHOD_NAME_ORDINAL, new String[0]);
		insertMethodCall(bsb, VARIABLE_NAME_PK, METHOD_NAME_PACK,
				new String[] { fa.toString() });
		insertSemicolon(bsb);
		addPublicMethodDecl(sb, METHOD_NAME_PACK, void.class, new Class[] {
				Packer.class, Object.class }, new String[] { VARIABLE_NAME_PK,
				VARIABLE_NAME_OBJECT }, new Class[] { IOException.class }, bsb
				.toString());
		LOG.trace("pack method src: " + sb.toString());
		try {
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(),
					packerCtClass);
			packerCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
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
		LOG.trace("unpack method src: " + sb.toString());
		try {
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(),
					unpackerCtClass);
			unpackerCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
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
		} else if (c.equals(Boolean.class) || c.equals(Byte.class)
				|| c.equals(Double.class) || c.equals(Float.class)
				|| c.equals(Integer.class) || c.equals(Long.class)
				|| c.equals(Short.class)) {
			// reference type (wrapper type)
			insertCodeOfUnpackMethodCallForWrapTypes(sb, f, c);
		} else if (c.equals(BigInteger.class) || c.equals(String.class)
				|| c.equals(byte[].class)) {
			// reference type (other type)
			insertCodeOfUnpackMethodCallForPrimTypes(sb, f, c);
		} else if (List.class.isAssignableFrom(c)) {
			// List
			insertCodeOfUnpackMethodCallForListType(sb, f, c);
		} else if (Map.class.isAssignableFrom(c)) {
			// Map
			insertCodeOfUnpackMethodCallForMapType(sb, f, c);
		} else if (CustomUnpacker.isRegistered(c)) {
			insertCodeOfUnpackMethodCallForRegisteredType(sb, f, c);
		} else if (MessageUnpackable.class.isAssignableFrom(c)) {
			// MessageUnpackable
			insertCodeOfUnpackMethodCallForMsgUnpackableType(sb, f, c);
		} else if (CustomMessage.isAnnotated(c, MessagePackMessage.class)) {
			// @MessagePackMessage
			Template tmpl = DynamicCodeGenTemplate.create(c);
			CustomMessage.registerTemplate(c, tmpl);
			insertCodeOfUnpackMethodCallForRegisteredType(sb, f, c);
		} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
			// FIXME DelegatePacker
			UnsupportedOperationException e = new UnsupportedOperationException(
					"not supported yet. : " + c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		} else if (CustomMessage.isAnnotated(c, MessagePackOrdinalEnum.class)) {
			// @MessagePackOrdinalEnum
			Template tmpl = DynamicCodeGenOrdinalEnumTemplate.create(c);
			CustomMessage.registerTemplate(c, tmpl);
			insertCodeOfUnpackMethodCallForRegisteredType(sb, f, c);
		} else {
			MessageTypeException e = new MessageTypeException("unknown type:  "
					+ c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		}
	}

	private void insertCodeOfUnpackMethodCallForPrimTypes(StringBuilder sb,
			Field f, Class<?> c) {
		if (f != null) {
			insertFieldAccess(sb, VARIABLE_NAME_TARGET, f.getName());
			insertInsertion(sb);
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
			insertFieldAccess(sb, VARIABLE_NAME_TARGET, f.getName());
			insertInsertion(sb);
		}
		StringBuilder mc = new StringBuilder();
		insertMethodCall(mc, VARIABLE_NAME_PK, getUnpackMethodName(c),
				new String[0]);
		insertMethodCall(sb, c.getName(), METHOD_NAME_VALUEOF,
				new String[] { mc.toString() });
		if (f != null) {
			insertSemicolon(sb);
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
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
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
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
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
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
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
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
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

	private void insertCodeOfUnpackMethodCallForRegisteredType(
			StringBuilder sb, Field f, Class<?> c) {
		// target.field = (Cast) CustomUnpacker.get(C.class).unpack(pk);
		StringBuilder mc = new StringBuilder();
		insertMethodCall(mc, CustomUnpacker.class.getName(), METHOD_NAME_GET,
				new String[] { c.getName() + ".class" });
		String t = mc.toString();
		mc = new StringBuilder();
		insertMethodCall(mc, t, METHOD_NAME_UNPACK,
				new String[] { VARIABLE_NAME_PK });
		t = mc.toString();
		mc = new StringBuilder();
		insertTypeCast(mc, c, t);
		insertFieldAccess(sb, VARIABLE_NAME_TARGET, f.getName());
		insertValueInsertion(sb, mc.toString());
		insertSemicolon(sb);
	}

	private void insertCodeOfUnpackMethodCallForMsgUnpackableType(
			StringBuilder sb, Field f, Class<?> c) {
		// if (t.fi == null) { t.fi = new Foo(); }
		sb.append(KEYWORD_IF);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
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
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
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
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
		sb.append(f.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
	}

	private void addUnpackMethodForOrdinalEnumTypes(CtClass unpackerCtClass,
			Class<?> c) {
		// Object unpack(Unpacker pac) throws IOException, MessageTypeException;
		StringBuilder sb = new StringBuilder();
		StringBuilder bsb = new StringBuilder();
		insertMethodCall(bsb, VARIABLE_NAME_PK, METHOD_NAME_UNPACKARRAY,
				new String[0]);
		insertSemicolon(bsb);
		StringBuilder mc = new StringBuilder();
		insertMethodCall(mc, VARIABLE_NAME_PK, METHOD_NAME_UNPACKINT,
				new String[0]);
		insertLocalVariableDecl(bsb, int.class, VARIABLE_NAME_I);
		insertValueInsertion(bsb, mc.toString());
		insertSemicolon(bsb);
		mc = new StringBuilder();
		insertMethodCall(mc, c.getName() + ".class",
				METHOD_NAME_GETENUMCONSTANTS, new String[0]);
		mc.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		mc.append(VARIABLE_NAME_I);
		mc.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		insertReturnStat(bsb, mc.toString());
		insertSemicolon(bsb);
		addPublicMethodDecl(sb, METHOD_NAME_UNPACK, Object.class,
				new Class<?>[] { Unpacker.class },
				new String[] { VARIABLE_NAME_PK }, new Class<?>[] {
						MessageTypeException.class, IOException.class }, bsb
						.toString());
		LOG.trace("unpack method src: " + sb.toString());
		try {
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(),
					unpackerCtClass);
			unpackerCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	public void addConvertMethod(CtClass tmplCtClass, Class<?> c, Field[] fs) {
		// Object convert(MessagePackObject from) throws MessageTypeException;
		StringBuilder sb = new StringBuilder();
		StringBuilder bsb = new StringBuilder();
		insertConvertMethodBody(bsb, c, fs);
		addPublicMethodDecl(sb, METHOD_NAME_CONVERT, Object.class,
				new Class<?>[] { MessagePackObject.class },
				new String[] { VARIABLE_NAME_MPO },
				new Class<?>[] { MessageTypeException.class }, bsb.toString());
		LOG.trace("convert method src: " + sb.toString());
		try {
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), tmplCtClass);
			tmplCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	private void insertConvertMethodBody(StringBuilder sb, Class<?> c,
			Field[] fs) {
		insertLocalVariableDecl(sb, c, VARIABLE_NAME_TARGET);
		StringBuilder mc = new StringBuilder();
		insertDefaultConsCall(mc, c);
		insertValueInsertion(sb, mc.toString());
		insertSemicolon(sb);
		insertCodeOfMessagePackObjectArrayGet(sb);
		insertCodeOfConvertMethodCalls(sb, fs);
		insertReturnStat(sb, VARIABLE_NAME_TARGET);
		insertSemicolon(sb);
	}

	private void insertCodeOfMessagePackObjectArrayGet(StringBuilder sb) {
		// MessagePackObject[] ary = obj.asArray();
		insertLocalVariableDecl(sb, MessagePackObject.class, VARIABLE_NAME_ARRAY, 1);
		StringBuilder mc = new StringBuilder();
		insertMethodCall(mc, VARIABLE_NAME_MPO, METHOD_NAME_ASARRAY, new String[0]);
		insertValueInsertion(sb, mc.toString());
		insertSemicolon(sb);
	}

	private void insertCodeOfConvertMethodCalls(StringBuilder sb, Field[] fields) {
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfConvertMethodCall(sb, fields[i], fields[i].getType(),
					i, null);
		}
	}

	private void insertCodeOfConvertMethodCall(StringBuilder sb, Field f,
			Class<?> c, int i, String v) {
		if (c.isPrimitive()) { // primitive type
			insertCodeOfConvertMethodCallForPrimTypes(sb, f, c, i, v);
		} else if (c.equals(Boolean.class) || c.equals(Byte.class)
				|| c.equals(Short.class) || c.equals(Integer.class)
				|| c.equals(Float.class) || c.equals(Long.class)
				|| c.equals(Double.class)) {
			// reference type (wrapper)
			insertCodeOfConvertMethodCallForWrapTypes(sb, f, c, i, v);
		} else if (c.equals(String.class) || c.equals(byte[].class)
				|| c.equals(BigInteger.class)) {
			insertCodeOfConvertMethodCallForPrimTypes(sb, f, c, i, v);
		} else if (List.class.isAssignableFrom(c)) {
			insertCodeOfConvertMethodCallForList(sb, f, c, i);
		} else if (Map.class.isAssignableFrom(c)) {
			insertCodeOfConvertMethodCallForMapType(sb, f, c, i);
		} else if (MessageConvertable.class.isAssignableFrom(c)) {
			insertCodeOfMessageConvertCallForMsgConvtblType(sb, f, c, i);
		} else if (CustomConverter.isRegistered(c)) {
			insertCodeOfMessageConvertCallForRegisteredType(sb, f, c, i);
		} else if (CustomMessage.isAnnotated(c, MessagePackMessage.class)) {
			// @MessagePackMessage
			Template tmpl = DynamicCodeGenTemplate.create(c);
			CustomMessage.registerTemplate(c, tmpl);
			insertCodeOfMessageConvertCallForRegisteredType(sb, f, c, i);
		} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
			// FIXME DelegatePacker
			UnsupportedOperationException e = new UnsupportedOperationException(
					"not supported yet. : " + c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		} else if (CustomMessage.isAnnotated(c, MessagePackOrdinalEnum.class)) {
			// @MessagePackMessage
			Template tmpl = DynamicCodeGenOrdinalEnumTemplate.create(c);
			CustomMessage.registerTemplate(c, tmpl);
			insertCodeOfMessageConvertCallForRegisteredType(sb, f, c, i);
		} else {
			MessageTypeException e = new MessageTypeException("Type error: "
					+ c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		}
	}

	private void insertCodeOfMessageConvertCallForRegisteredType(
			StringBuilder sb, Field f, Class<?> c, int i) {
		// ((MessageConvertable)f_i).messageConvert(ary[i]);
		// obj = tmpl.convert(mpo);
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
		sb.append(f.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(c.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CustomConverter.class.getName());
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_GET);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(c.getName() + ".class");
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_CONVERT);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(VARIABLE_NAME_ARRAY);
		sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		sb.append(i);
		sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		insertSemicolon(sb);
	}

	private void insertCodeOfMessageConvertCallForMsgConvtblType(
			StringBuilder sb, Field f, Class<?> c, int i) {
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

		// ((MessageConvertable)f_i).messageConvert(ary[i]);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(MessageConvertable.class.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(f.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_MSGCONVERT);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(VARIABLE_NAME_ARRAY);
		sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		sb.append(i);
		sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
	}

	private void insertCodeOfConvertMethodCallForPrimTypes(StringBuilder sb,
			Field f, Class<?> c, int i, String name) {
		// target.f0 = objs[0].intValue();
		if (f != null) {
			sb.append(VARIABLE_NAME_TARGET);
			sb.append(CHAR_NAME_DOT);
			sb.append(f.getName());
			sb.append(CHAR_NAME_SPACE);
			sb.append(CHAR_NAME_EQUAL);
			sb.append(CHAR_NAME_SPACE);
			sb.append(VARIABLE_NAME_ARRAY);
			sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(i);
			sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		} else {
			sb.append(name);
		}
		sb.append(CHAR_NAME_DOT);
		sb.append(getAsMethodName(c));
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		if (f != null) {
			insertSemicolon(sb);
		}
	}

	private void insertCodeOfConvertMethodCallForWrapTypes(StringBuilder sb,
			Field f, Class<?> c, int i, String v) {
		if (f != null) {
			sb.append(VARIABLE_NAME_TARGET);
			sb.append(CHAR_NAME_DOT);
			sb.append(f.getName());
			sb.append(CHAR_NAME_SPACE);
			sb.append(CHAR_NAME_EQUAL);
			sb.append(CHAR_NAME_SPACE);
		}
		sb.append(KEYWORD_NEW);
		sb.append(CHAR_NAME_SPACE);
		sb.append(c.getName());
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		if (f != null) {
			sb.append(VARIABLE_NAME_ARRAY);
			sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(i);
			sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		} else {
			sb.append(v);
		}
		sb.append(CHAR_NAME_DOT);
		sb.append(getAsMethodName(c));
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		if (f != null) {
			insertSemicolon(sb);
		}
	}

	private void insertCodeOfConvertMethodCallForList(StringBuilder sb,
			Field field, Class<?> type, int i) {
		ParameterizedType generic = (ParameterizedType) field.getGenericType();
		Class<?> genericType = (Class<?>) generic.getActualTypeArguments()[0];

		// List<MessagePackObject> list = ary[i].asList();
		sb.append(List.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_LIST);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_ARRAY);
		sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		sb.append(i);
		sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_ASLIST);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// int size = list.size();
		sb.append(int.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_SIZE);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_LIST);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_SIZE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// field initializer
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
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

		// block begin
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		sb.append(MessagePackObject.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_VAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(MessagePackObject.class.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(VARIABLE_NAME_LIST);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_GET);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(VARIABLE_NAME_I);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
		sb.append(field.getName());
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_ADD);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		insertCodeOfConvertMethodCall(sb, null, genericType, -1,
				VARIABLE_NAME_VAL);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		// block end
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
	}

	private void insertCodeOfConvertMethodCallForMapType(StringBuilder sb,
			Field f, Class<?> c, int i) {
		ParameterizedType generic = (ParameterizedType) f.getGenericType();
		Class<?> genericType0 = (Class<?>) generic.getActualTypeArguments()[0];
		Class<?> genericType1 = (Class<?>) generic.getActualTypeArguments()[1];

		// Map<MessagePackObject, MessagePackObject> map = ary[i].asMap();
		sb.append(Map.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_MAP);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_ARRAY);
		sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		sb.append(i);
		sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		sb.append(CHAR_NAME_DOT);
		sb.append("asMap");
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// int size = list.size();
		sb.append(int.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_SIZE);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_MAP);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_SIZE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		// field initializer
		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
		sb.append(f.getName());
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
		sb.append(Iterator.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_ITER);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_MAP);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_KEYSET);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_ITERATOR);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_ITER);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_HASNEXT);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);

		// block map.
		sb.append(MessagePackObject.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_KEY);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(MessagePackObject.class.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(VARIABLE_NAME_ITER);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_NEXT);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
		sb.append(MessagePackObject.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_VAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(MessagePackObject.class.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(VARIABLE_NAME_MAP);
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_GET);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(VARIABLE_NAME_KEY);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		sb.append(VARIABLE_NAME_TARGET);
		sb.append(CHAR_NAME_DOT);
		sb.append(f.getName());
		sb.append(CHAR_NAME_DOT);
		sb.append(METHOD_NAME_PUT);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		insertCodeOfConvertMethodCall(sb, null, genericType0, -1,
				VARIABLE_NAME_KEY);
		sb.append(CHAR_NAME_COMMA);
		sb.append(CHAR_NAME_SPACE);
		insertCodeOfConvertMethodCall(sb, null, genericType1, -1,
				VARIABLE_NAME_VAL);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);

		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
	}

	public void addConvertMethodForOrdinalEnumTypes(CtClass tmplCtClass,
			Class<?> c) {
		// Object convert(MessagePackObject from) throws MessageTypeException;
		StringBuilder sb = new StringBuilder();
		StringBuilder bsb = new StringBuilder();
		insertCodeOfMessagePackObjectArrayGet(bsb);
		StringBuilder mc = new StringBuilder();
		insertMethodCall(mc, VARIABLE_NAME_ARRAY + "[0]", METHOD_NAME_ASINT,
				new String[0]);
		insertLocalVariableDecl(bsb, int.class, VARIABLE_NAME_I);
		insertValueInsertion(bsb, mc.toString());
		insertSemicolon(bsb);
		mc = new StringBuilder();
		insertMethodCall(mc, c.getName() + ".class",
				METHOD_NAME_GETENUMCONSTANTS, new String[0]);
		mc.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		mc.append(VARIABLE_NAME_I);
		mc.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		insertLocalVariableDecl(bsb, Object.class, VARIABLE_NAME_OBJECT);
		insertValueInsertion(bsb, mc.toString());
		insertSemicolon(bsb);
		mc = new StringBuilder();
		insertTypeCast(mc, c, VARIABLE_NAME_OBJECT);
		insertReturnStat(bsb, mc.toString());
		insertSemicolon(bsb);
		addPublicMethodDecl(sb, METHOD_NAME_CONVERT, Object.class,
				new Class<?>[] { MessagePackObject.class },
				new String[] { VARIABLE_NAME_MPO },
				new Class<?>[] { MessageTypeException.class }, bsb.toString());
		LOG.trace("convert method src: " + sb.toString());
		try {
			CtMethod newCtMethod = CtNewMethod.make(sb.toString(), tmplCtClass);
			tmplCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	private Class<?> createClass(CtClass packerCtClass)
			throws CannotCompileException {
		return packerCtClass.toClass(null, null);
	}
}
