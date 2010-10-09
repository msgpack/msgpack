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

import javassist.CannotCompileException;
import javassist.CtClass;
import javassist.CtMethod;
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

class DynamicCodeGen extends DynamicCodeGenBase implements Constants {

	private static Logger LOG = LoggerFactory.getLogger(DynamicCodeGen.class);

	private static DynamicCodeGen INSTANCE;

	public static DynamicCodeGen getInstance() {
		if (INSTANCE == null) {
			LOG.info("create an instance of the type: "
					+ DynamicCodeGen.class.getName());
			INSTANCE = new DynamicCodeGen();
		}
		return INSTANCE;
	}

	private ConcurrentHashMap<String, Template[]> tmplCache;

	DynamicCodeGen() {
		super();
		tmplCache = new ConcurrentHashMap<String, Template[]>();
	}

	public void setTemplates(Class<?> type, Template[] tmpls) {
		tmplCache.putIfAbsent(type.getName(), tmpls);
	}

	public Template[] getTemplates(Class<?> type) {
		return tmplCache.get(type.getName());
	}

	public Class<?> generateMessagePackerClass(Class<?> origClass) {
		try {
			LOG.debug("start generating a packer class for "
					+ origClass.getName());
			String origName = origClass.getName();
			String packerName = origName + POSTFIX_TYPE_NAME_PACKER + inc();
			checkTypeValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass packerCtClass = pool.makeClass(packerName);
			setInterface(packerCtClass, MessagePacker.class);
			addDefaultConstructor(packerCtClass);
			Field[] fields = getDeclaredFields(origClass);
			addPackMethod(packerCtClass, origClass, fields, false);
			Class<?> packerClass = createClass(packerCtClass);
			LOG.debug("generated a packer class for " + origClass.getName());
			return packerClass;
		} catch (NotFoundException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateOrdinalEnumPackerClass(Class<?> origClass) {
		try {
			LOG.debug("start generating an enum packer for "
					+ origClass.getName());
			String origName = origClass.getName();
			String packerName = origName + POSTFIX_TYPE_NAME_PACKER + inc();
			checkTypeValidation(origClass);
			CtClass packerCtClass = pool.makeClass(packerName);
			setInterface(packerCtClass, MessagePacker.class);
			addDefaultConstructor(packerCtClass);
			addPackMethod(packerCtClass, origClass, null, true);
			Class<?> packerClass = createClass(packerCtClass);
			LOG.debug("generated an enum class for " + origClass.getName());
			return packerClass;
		} catch (NotFoundException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (CannotCompileException e) {
			LOG.error(e.getMessage(), e);
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}

	public Class<?> generateTemplateClass(Class<?> origClass) {
		try {
			LOG.debug("start generating a template class for "
					+ origClass.getName());
			String origName = origClass.getName();
			String tmplName = origName + POSTFIX_TYPE_NAME_TEMPLATE + inc();
			checkTypeValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass tmplCtClass = pool.makeClass(tmplName);
			setInterface(tmplCtClass, Template.class);
			setInterface(tmplCtClass, DynamicCodeGenBase.TemplateAccessor.class);
			addDefaultConstructor(tmplCtClass);
			Field[] fields = getDeclaredFields(origClass);
			Template[] tmpls = createTemplates(fields);
			setTemplates(origClass, tmpls);
			addTemplateArrayField(tmplCtClass);
			addSetTemplatesMethod(tmplCtClass);
			addUnpackMethod(tmplCtClass, origClass, fields, false);
			addConvertMethod(tmplCtClass, origClass, fields, false);
			Class<?> tmplClass = createClass(tmplCtClass);
			LOG.debug("generated a template class for " + origClass.getName());
			return tmplClass;
		} catch (NotFoundException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	public Class<?> generateOrdinalEnumTemplateClass(Class<?> origClass) {
		try {
			LOG.debug("start generating a enum template class for "
					+ origClass.getName());
			String origName = origClass.getName();
			checkTypeValidation(origClass);
			String tmplName = origName + POSTFIX_TYPE_NAME_TEMPLATE + inc();
			CtClass tmplCtClass = pool.makeClass(tmplName);
			setInterface(tmplCtClass, Template.class);
			addDefaultConstructor(tmplCtClass);
			addUnpackMethod(tmplCtClass, origClass, null, true);
			addConvertMethod(tmplCtClass, origClass, null, true);
			// addConvertMethodForOrdinalEnumTypes(tmplCtClass, origClass);
			Class<?> tmplClass = createClass(tmplCtClass);
			LOG.debug("generated an enum template class for "
					+ origClass.getName());
			return tmplClass;
		} catch (NotFoundException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	@Override
	public void checkTypeValidation(Class<?> origClass) {
		// not public, abstract
		int mod = origClass.getModifiers();
		if ((!Modifier.isPublic(mod)) || Modifier.isAbstract(mod)) {
			throwTypeValidationException(origClass,
					"a class must have a public modifier");
		}
		// interface
		if (origClass.isInterface()) {
			throwTypeValidationException(origClass,
					"cannot generate packer and unpacker for an interface");
		}
	}

	@Override
	public void checkDefaultConstructorValidation(Class<?> origClass) {
		// check that the zero-argument constructor exists
		Constructor<?> cons = null;
		try {
			cons = origClass.getDeclaredConstructor(new Class[0]);
		} catch (Exception e) {
			throwConstructorValidationException(origClass);
		}

		// check the modifiers
		int mod = cons.getModifiers();
		if (!Modifier.isPublic(mod)) {
			throwConstructorValidationException(origClass);
		}
	}

	Field[] getDeclaredFields(Class<?> origClass) {
		ArrayList<Field> allFields = new ArrayList<Field>();
		Class<?> nextClass = origClass;
		while (nextClass != Object.class) {
			Field[] fields = nextClass.getDeclaredFields();
			for (Field field : fields) {
				try {
					checkFieldValidation(field, allFields);
					allFields.add(field);
				} catch (DynamicCodeGenException e) { // ignore
					LOG.error(e.getMessage(), e);
				}
			}
			nextClass = nextClass.getSuperclass();
		}
		return allFields.toArray(new Field[0]);
	}

	void checkFieldValidation(Field field, List<Field> fields) {
		// check that it has a public modifier
		int mod = field.getModifiers();
		if ((!(Modifier.isPublic(mod))) || Modifier.isStatic(mod)
				|| Modifier.isFinal(mod) || Modifier.isTransient(mod)
				|| field.isSynthetic()) {
			throwFieldValidationException(field);
		}
		// check same name
		for (Field f : fields) {
			if (f.getName().equals(field.getName())) {
				throwFieldValidationException(field);
			}
		}
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

	private void addPackMethod(CtClass packerCtClass, Class<?> c, Field[] fs,
			boolean isEnum) {
		// void pack(Packer pk, Object target) throws IOException;
		StringBuilder sb = new StringBuilder();
		if (!isEnum) {
			insertPackMethodBody(sb, c, fs);
		} else {
			insertOrdinalEnumPackMethodBody(sb, c);
		}
		try {
			LOG.trace("pack method src: " + sb.toString());
			int mod = javassist.Modifier.PUBLIC;
			CtClass returnType = classToCtClass(void.class);
			String mname = METHOD_NAME_PACK;
			CtClass[] paramTypes = new CtClass[] {
					classToCtClass(Packer.class), classToCtClass(Object.class) };
			CtClass[] exceptTypes = new CtClass[] { classToCtClass(IOException.class) };
			CtMethod newCtMethod = CtNewMethod.make(mod, returnType, mname,
					paramTypes, exceptTypes, sb.toString(), packerCtClass);
			packerCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		} catch (NotFoundException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	private void insertPackMethodBody(StringBuilder sb, Class<?> type,
			Field[] fields) {
		// void pack(Packer packer, Object target) throws IOException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		String typeName = classToString(type);
		Object[] args0 = new Object[] { typeName, typeName };
		sb.append(String.format(STATEMENT_PACKER_PACKERMETHODBODY_01, args0));
		Object[] args1 = new Object[] { fields.length };
		sb.append(String.format(STATEMENT_PACKER_PACKERMETHODBODY_02, args1));
		for (Field f : fields) {
			insertCodeOfPackMethodCall(sb, f);
		}
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
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
			MessagePacker packer = DynamicPacker.create(c);
			CustomMessage.registerPacker(c, packer);
		} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
			// FIXME DelegatePacker
			UnsupportedOperationException e = new UnsupportedOperationException(
					"not supported yet. : " + c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		} else if (CustomMessage.isAnnotated(c, MessagePackOrdinalEnum.class)) {
			// @MessagePackOrdinalEnum
			MessagePacker packer = DynamicOrdinalEnumPacker.create(c);
			CustomMessage.registerPacker(c, packer);
		} else {
			MessageTypeException e = new MessageTypeException("unknown type: "
					+ c.getName());
			LOG.error(e.getMessage(), e);
			throw e;
		}
		Object[] args = new Object[] { field.getName() };
		sb.append(String.format(STATEMENT_PACKER_PACKERMETHODBODY_03, args));
	}

	private void insertOrdinalEnumPackMethodBody(StringBuilder sb, Class<?> c) {
		// void pack(Packer packer, Object target) throws IOException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		String typeName = classToString(c);
		Object[] args0 = new Object[] { typeName, typeName };
		sb.append(String.format(STATEMENT_PACKER_PACKERMETHODBODY_01, args0));
		Object[] args1 = new Object[] { 1 };
		sb.append(String.format(STATEMENT_PACKER_PACKERMETHODBODY_02, args1));
		Object[] args2 = new Object[0];
		sb.append(String.format(STATEMENT_PACKER_PACKERMETHODBODY_04, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}

	private void addUnpackMethod(CtClass tmplCtClass, Class<?> type,
			Field[] fields, boolean isEnum) {
		// Object unpack(Unpacker u) throws IOException, MessageTypeException;
		StringBuilder sb = new StringBuilder();
		if (!isEnum) {
			insertUnpackMethodBody(sb, type, fields);
		} else {
			insertOrdinalEnumUnpackMethodBody(sb, type);
		}
		try {
			LOG.trace("unpack method src: " + sb.toString());
			int mod = javassist.Modifier.PUBLIC;
			CtClass returnType = classToCtClass(Object.class);
			String mname = METHOD_NAME_UNPACK;
			CtClass[] paramTypes = new CtClass[] { classToCtClass(Unpacker.class) };
			CtClass[] exceptTypes = new CtClass[] {
					classToCtClass(IOException.class),
					classToCtClass(MessageTypeException.class) };
			CtMethod newCtMethod = CtNewMethod.make(mod, returnType, mname,
					paramTypes, exceptTypes, sb.toString(), tmplCtClass);
			tmplCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		} catch (NotFoundException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	private void insertUnpackMethodBody(StringBuilder sb, Class<?> type,
			Field[] fields) {
		// Object unpack(Unpacker u) throws IOException, MessageTypeException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		// Foo _$$_t = new Foo();
		String typeName = classToString(type);
		Object[] args0 = new Object[] { typeName, typeName };
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_01, args0));
		// $1.unpackArray();
		Object[] args1 = new Object[0];
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_02, args1));
		insertCodeOfUnpackMethodCalls(sb, fields);
		// return _$$_t;
		Object[] args2 = new Object[0];
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_04, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}

	private void insertCodeOfUnpackMethodCalls(StringBuilder sb, Field[] fields) {
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfUnpackMethodCall(sb, fields[i], i);
		}
	}

	private void insertCodeOfUnpackMethodCall(StringBuilder sb, Field field,
			int i) {
		// target.fi = ((Integer)_$$_tmpls[i].unpack(_$$_pk)).intValue();
		Class<?> returnType = field.getType();
		boolean isPrim = returnType.isPrimitive();
		Object[] args = new Object[] {
				field.getName(),
				isPrim ? "(" : "",
				isPrim ? getPrimToWrapperType(returnType).getName()
						: classToString(returnType),
				i,
				isPrim ? ")." + getPrimTypeValueMethodName(returnType) + "()"
						: "" };
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_03, args));
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

	private void insertOrdinalEnumUnpackMethodBody(StringBuilder sb,
			Class<?> type) {
		// Object unpack(Unpacker u) throws IOException, MessageTypeException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		// $1.unpackArray();
		Object[] args0 = new Object[0];
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_02, args0));
		// int i = $1.unapckInt();
		Object[] args1 = new Object[0];
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_05, args1));
		// return Foo.class.getEnumConstants()[i];
		Object[] args2 = new Object[] { classToString(type) };
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_06, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}

	public void addConvertMethod(CtClass tmplCtClass, Class<?> type,
			Field[] fields, boolean isEnum) {
		// Object convert(MessagePackObject mpo) throws MessageTypeException;
		StringBuilder sb = new StringBuilder();
		if (!isEnum) {
			insertConvertMethodBody(sb, type, fields);
		} else {
			insertOrdinalEnumConvertMethodBody(sb, type);
		}
		try {
			LOG.trace("convert method src: " + sb.toString());
			int mod = javassist.Modifier.PUBLIC;
			CtClass returnType = classToCtClass(Object.class);
			String mname = METHOD_NAME_CONVERT;
			CtClass[] paramTypes = new CtClass[] { classToCtClass(MessagePackObject.class) };
			CtClass[] exceptTypes = new CtClass[] { classToCtClass(MessageTypeException.class) };
			CtMethod newCtMethod = CtNewMethod.make(mod, returnType, mname,
					paramTypes, exceptTypes, sb.toString(), tmplCtClass);
			tmplCtClass.addMethod(newCtMethod);
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		} catch (NotFoundException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e
					.getMessage()
					+ ": " + sb.toString(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		}
	}

	private void insertConvertMethodBody(StringBuilder sb, Class<?> type,
			Field[] fields) {
		// Object convert(MessagePackObject mpo) throws MessageTypeException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		// Foo _$$_t = new Foo();
		String typeName = classToString(type);
		Object[] args0 = new Object[] { typeName, typeName };
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_01, args0));
		// MessagePackObject[] _$$_ary = $1.asArray();
		Object[] args1 = new Object[] { classToString(MessagePackObject[].class) };
		sb.append(String.format(STATEMENT_PACKER_CONVERTMETHODBODY_01, args1));
		insertCodeOfConvertMethodCalls(sb, fields);
		// return _$$_t;
		Object[] args2 = new Object[0];
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_04, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}

	private void insertCodeOfConvertMethodCalls(StringBuilder sb, Field[] fields) {
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfConvMethodCall(sb, fields[i], i);
		}
	}

	private void insertCodeOfConvMethodCall(StringBuilder sb, Field field, int i) {
		// target.fi = ((Object)_$$_tmpls[i].convert(_$$_ary[i])).intValue();
		Class<?> returnType = field.getType();
		boolean isPrim = returnType.isPrimitive();
		Object[] args = new Object[] {
				field.getName(),
				isPrim ? "(" : "",
				isPrim ? getPrimToWrapperType(returnType).getName()
						: classToString(returnType),
				i,
				i,
				isPrim ? ")." + getPrimTypeValueMethodName(returnType) + "()"
						: "" };
		sb.append(String.format(STATEMENT_PACKER_CONVERTMETHODBODY_02, args));
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

	private void insertOrdinalEnumConvertMethodBody(StringBuilder sb,
			Class<?> type) {
		// Object convert(MessagePackObject mpo) throws MessageTypeException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		// MessagePackObject[] _$$_ary = $1.asArray();
		Object[] args0 = new Object[] { classToString(MessagePackObject[].class) };
		sb.append(String.format(STATEMENT_PACKER_CONVERTMETHODBODY_01, args0));
		// int i = _$$_ary[0].asInt();
		Object[] args1 = new Object[0];
		sb.append(String.format(STATEMENT_PACKER_CONVERTMETHODBODY_03, args1));
		// return Foo.class.getEnumConstants()[i];
		Object[] args2 = new Object[] { classToString(type) };
		sb.append(String.format(STATEMENT_PACKER_UNPACKERMETHODBODY_06, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}
}
