package org.msgpack.util.codegen;

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
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

	private ConcurrentHashMap<String, Template[]> tmplMap;

	DynamicCodeGen() {
		pool = ClassPool.getDefault();
		tmplMap = new ConcurrentHashMap<String, Template[]>();
	}

	public void setTemplates(Class<?> origClass, Template[] tmpls) {
		tmplMap.putIfAbsent(origClass.getName(), tmpls);
	}

	public Template[] getTemplates(Class<?> origClass) {
		return tmplMap.get(origClass.getName());
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

	public Class<?> generateTemplateClass(Class<?> origClass) {
		LOG.debug("start generating a Template impl.: " + origClass.getName());
		try {
			String origName = origClass.getName();
			String tmplName = origName + POSTFIX_TYPE_NAME_TEMPLATE + inc();
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass tmplCtClass = pool.makeClass(tmplName);
			CtClass acsCtClass = pool.get(TemplateAccessorImpl.class.getName());
			setInterface(tmplCtClass, Template.class);
			setInterface(tmplCtClass, DynamicCodeGenBase.TemplateAccessor.class);
			addDefaultConstructor(tmplCtClass);
			Field[] fields = getDeclaredFields(origClass);
			Template[] tmpls = createTemplates(fields);
			setTemplates(origClass, tmpls);
			addTemplateArrayField(tmplCtClass, acsCtClass);
			addSetTemplatesMethod(tmplCtClass, acsCtClass);
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
			checkClassValidation(origClass);
			CtClass tmplCtClass = makeClass(origName);
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

	private CtClass makeClass(String origName) throws NotFoundException {
		StringBuilder sb = new StringBuilder();
		sb.append(origName);
		sb.append(POSTFIX_TYPE_NAME_TEMPLATE);
		sb.append(inc());
		String invokerName = sb.toString();
		CtClass newCtClass = pool.makeClass(invokerName);
		newCtClass.setModifiers(Modifier.PUBLIC);
		return newCtClass;
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

	Template[] createTemplates(Field[] fields) {
		Template[] tmpls = new Template[fields.length];
		for (int i = 0; i < tmpls.length; ++i) {
			tmpls[i] = createTemplate(fields[i]);
		}
		return tmpls;
	}

	Template createTemplate(Field field) {
		Class<?> c = field.getType();
		if (List.class.isAssignableFrom(c) || Map.class.isAssignableFrom(c)) {
			return createTemplate(field.getGenericType());
		} else {
			return createTemplate(c);
		}
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
			; // ignore
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

	private void addTemplateArrayField(CtClass newCtClass, CtClass acsCtClass)
			throws NotFoundException, CannotCompileException {
		CtField tmplsField = acsCtClass
				.getDeclaredField(VARIABLE_NAME_TEMPLATES);
		CtField tmplsField2 = new CtField(tmplsField.getType(), tmplsField
				.getName(), newCtClass);
		newCtClass.addField(tmplsField2);
	}

	private void addSetTemplatesMethod(CtClass newCtClass, CtClass acsCtClass)
			throws NotFoundException, CannotCompileException {
		CtMethod settmplsMethod = acsCtClass
				.getDeclaredMethod(METHOD_NAME_SETTEMPLATES);
		CtMethod settmplsMethod2 = CtNewMethod.copy(settmplsMethod, newCtClass,
				null);
		newCtClass.addMethod(settmplsMethod2);
	}

	private void addUnpackMethod(CtClass unpackerCtClass, Class<?> c, Field[] fs) {
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
		insertCodeOfUnpackMethodCalls(sb, fs);
		insertReturnStat(sb, VARIABLE_NAME_TARGET);
		insertSemicolon(sb);
	}

	private void insertCodeOfUnpackMethodCalls(StringBuilder sb, Field[] fields) {
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfUnpackMethodCall(sb, fields[i], i);
		}
	}

	private void insertCodeOfUnpackMethodCall(StringBuilder sb, Field field,
			int i) {
		// target.fi = ((Integer)_$$_tmpls[i].unpack(_$$_pk)).intValue();
		Class<?> type = field.getType();
		insertFieldAccess(sb, VARIABLE_NAME_TARGET, field.getName());
		String castType = null;
		String rawValueGetter = null;
		if (type.isPrimitive()) {
			if (type.equals(byte.class)) {
				castType = "(Byte)";
				rawValueGetter = "byteValue";
			} else if (type.equals(boolean.class)) {
				castType = "(Boolean)";
				rawValueGetter = "booleanValue";
			} else if (type.equals(short.class)) {
				castType = "(Short)";
				rawValueGetter = "shortValue";
			} else if (type.equals(int.class)) {
				castType = "(Integer)";
				rawValueGetter = "intValue";
			} else if (type.equals(long.class)) {
				castType = "(Long)";
				rawValueGetter = "longValue";
			} else if (type.equals(float.class)) {
				castType = "(Float)";
				rawValueGetter = "floatValue";
			} else if (type.equals(double.class)) {
				castType = "(Double)";
				rawValueGetter = "doubleValue";
			} else {
				throw new DynamicCodeGenException("Fatal error: "
						+ type.getName());
			}
		} else if (type.isArray()) {
			Class<?> ct = type.getComponentType();
			if (ct.equals(byte.class)) {
				castType = "(byte[])";
			} else {
				throw new UnsupportedOperationException("Not supported yet: "
						+ type.getName());
			}
		} else {
			castType = "(" + type.getName() + ")";
		}
		StringBuilder mc = new StringBuilder();
		mc.append(castType);
		mc.append(VARIABLE_NAME_TEMPLATES);
		mc.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		mc.append(i);
		mc.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		String tname = mc.toString();
		mc = new StringBuilder();
		insertMethodCall(mc, tname, METHOD_NAME_UNPACK,
				new String[] { VARIABLE_NAME_PK });
		if (type.isPrimitive()) {
			tname = mc.toString();
			mc = new StringBuilder();
			mc.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			mc.append(tname);
			mc.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			tname = mc.toString();
			mc = new StringBuilder();
			insertMethodCall(mc, tname, rawValueGetter, new String[0]);
		}
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
		insertLocalVariableDecl(sb, MessagePackObject.class,
				VARIABLE_NAME_ARRAY, 1);
		StringBuilder mc = new StringBuilder();
		insertMethodCall(mc, VARIABLE_NAME_MPO, METHOD_NAME_ASARRAY,
				new String[0]);
		insertValueInsertion(sb, mc.toString());
		insertSemicolon(sb);
	}

	private void insertCodeOfConvertMethodCalls(StringBuilder sb, Field[] fields) {
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfConvMethodCall(sb, fields[i], i);
		}
	}

	private void insertCodeOfConvMethodCall(StringBuilder sb, Field field, int i) {
		// target.f0 = ((Integer)_$$_tmpls[i].convert(_$$_ary[i])).intValue();
		Class<?> type = field.getType();
		insertFieldAccess(sb, VARIABLE_NAME_TARGET, field.getName());
		String castType = null;
		String rawValueGetter = null;
		if (type.isPrimitive()) {
			if (type.equals(byte.class)) {
				castType = "(Byte)";
				rawValueGetter = "byteValue";
			} else if (type.equals(boolean.class)) {
				castType = "(Boolean)";
				rawValueGetter = "booleanValue";
			} else if (type.equals(short.class)) {
				castType = "(Short)";
				rawValueGetter = "shortValue";
			} else if (type.equals(int.class)) {
				castType = "(Integer)";
				rawValueGetter = "intValue";
			} else if (type.equals(long.class)) {
				castType = "(Long)";
				rawValueGetter = "longValue";
			} else if (type.equals(float.class)) {
				castType = "(Float)";
				rawValueGetter = "floatValue";
			} else if (type.equals(double.class)) {
				castType = "(Double)";
				rawValueGetter = "doubleValue";
			} else {
				throw new DynamicCodeGenException("Fatal error: "
						+ type.getName());
			}
		} else if (type.isArray()) {
			Class<?> ct = type.getComponentType();
			if (ct.equals(byte.class)) {
				castType = "(byte[])";
			} else {
				throw new UnsupportedOperationException("Not supported yet: "
						+ type.getName());
			}
		} else {
			castType = "(" + type.getName() + ")";
		}
		StringBuilder mc = new StringBuilder();
		mc.append(castType);
		mc.append(VARIABLE_NAME_TEMPLATES);
		mc.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		mc.append(i);
		mc.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		String tname = mc.toString();
		mc = new StringBuilder();
		mc.append(VARIABLE_NAME_ARRAY);
		mc.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
		mc.append(i);
		mc.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		String aname = mc.toString();
		mc = new StringBuilder();
		insertMethodCall(mc, tname, METHOD_NAME_CONVERT, new String[] { aname });
		if (type.isPrimitive()) {
			tname = mc.toString();
			mc = new StringBuilder();
			mc.append(Constants.CHAR_NAME_LEFT_PARENTHESIS);
			mc.append(tname);
			mc.append(Constants.CHAR_NAME_RIGHT_PARENTHESIS);
			tname = mc.toString();
			mc = new StringBuilder();
			insertMethodCall(mc, tname, rawValueGetter, new String[0]);
		}
		insertValueInsertion(sb, mc.toString());
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
