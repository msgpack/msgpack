package org.msgpack.util.codegen;

import java.io.IOException;
import java.lang.annotation.Annotation;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import javassist.CannotCompileException;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.CtNewMethod;
import javassist.NotFoundException;

import org.msgpack.MessagePackObject;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackOptional;
import org.msgpack.packer.OptionalPacker;
import org.msgpack.template.OptionalTemplate;
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

	private ConcurrentHashMap<String, MessagePacker[]> pkCache;

	DynamicCodeGen() {
		super();
		tmplCache = new ConcurrentHashMap<String, Template[]>();
		pkCache = new ConcurrentHashMap<String, MessagePacker[]>();
	}

	public void setTemplates(Class<?> type, Template[] tmpls) {
		tmplCache.putIfAbsent(type.getName(), tmpls);
	}

	public Template[] getTemplates(Class<?> type) {
		return tmplCache.get(type.getName());
	}

	public void setMessagePackers(Class<?> type, MessagePacker[] pks) {
		pkCache.putIfAbsent(type.getName(), pks);
	}

	public MessagePacker[] getMessagePackers(Class<?> type) {
		return pkCache.get(type.getName());
	}

	public Class<?> generateMessagePackerClass(Class<?> origClass,
			List<FieldOption> fieldOpts) {
		try {
			LOG.debug("start generating a packer class for "
					+ origClass.getName());
			String origName = origClass.getName();
			String packerName = origName + POSTFIX_TYPE_NAME_PACKER + inc();
			checkTypeValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass packerCtClass = pool.makeClass(packerName);
			setSuperclass(packerCtClass, MessagePackerAccessorImpl.class);
			setInterface(packerCtClass, MessagePacker.class);
			addClassTypeConstructor(packerCtClass);
			Field[] fields = getDeclaredFields(origClass);
			MessagePacker[] packers = null;
			if (fieldOpts != null) {
				fields = sortFields(fields, fieldOpts);
				packers = createMessagePackers(fieldOpts);
			} else {
				packers = createMessagePackers(fields);
			}
			setMessagePackers(origClass, packers);
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
			setSuperclass(packerCtClass, MessagePackerAccessorImpl.class);
			setInterface(packerCtClass, MessagePacker.class);
			addClassTypeConstructor(packerCtClass);
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

	public Class<?> generateTemplateClass(Class<?> origClass,
			List<FieldOption> fieldOpts) {
		try {
			LOG.debug("start generating a template class for "
					+ origClass.getName());
			String origName = origClass.getName();
			String tmplName = origName + POSTFIX_TYPE_NAME_TEMPLATE + inc();
			checkTypeValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass tmplCtClass = pool.makeClass(tmplName);
			setSuperclass(tmplCtClass, TemplateAccessorImpl.class);
			setInterface(tmplCtClass, Template.class);
			addClassTypeConstructor(tmplCtClass);
			Field[] fields = getDeclaredFields(origClass);
			Template[] tmpls = null;
			if (fieldOpts != null) {
				fields = sortFields(fields, fieldOpts);
				tmpls = createTemplates(fieldOpts);
			} else {
				tmpls = createTemplates(fields);
			}
			setTemplates(origClass, tmpls);
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
			setSuperclass(tmplCtClass, TemplateAccessorImpl.class);
			setInterface(tmplCtClass, Template.class);
			addClassTypeConstructor(tmplCtClass);
			addUnpackMethod(tmplCtClass, origClass, null, true);
			addConvertMethod(tmplCtClass, origClass, null, true);
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
					LOG.trace(e.getMessage(), e);
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

	Field[] sortFields(Field[] fields, List<FieldOption> fieldOpts) {
		if (fields.length != fieldOpts.size()) {
			throwFieldSortingException(String.format(
					"Mismatch: public field num: %d, option num: %d",
					new Object[] { fields.length, fieldOpts.size() }));
		}
		Field[] sorted = new Field[fields.length];
		for (int i = 0; i < sorted.length; ++i) {
			FieldOption opt = fieldOpts.get(i);
			Field match = null;
			for (Field f : fields) {
				if (opt.name.equals(f.getName())) {
					match = f;
					break;
				}
			}
			if (match != null) {
				sorted[i] = match;
			} else {
				throwFieldSortingException(String.format(
						"Mismatch: a %s field option is not declared",
						new Object[] { opt.name }));
			}
		}
		return sorted;
	}

	MessagePacker[] createMessagePackers(List<FieldOption> fieldOpts) {
		MessagePacker[] pks = new MessagePacker[fieldOpts.size()];
		for (int i = 0; i < pks.length; ++i) {
			pks[i] = toMessagePacker(fieldOpts.get(i).tmpl);
		}
		return pks;
	}

	MessagePacker[] createMessagePackers(Field[] fields) {
		MessagePacker[] pks = new MessagePacker[fields.length];
		for (int i = 0; i < pks.length; ++i) {
			pks[i] = createMessagePacker(fields[i]);
		}
		return pks;
	}

	MessagePacker createMessagePacker(Field field) {
		boolean isOptional = isAnnotated(field, MessagePackOptional.class);
		Class<?> c = field.getType();
		MessagePacker pk = null;
		if (List.class.isAssignableFrom(c) || Map.class.isAssignableFrom(c)) {
			pk = createMessagePacker(field.getGenericType());
		} else {
			pk = createMessagePacker(c);
		}
		if (isOptional) {
			return new OptionalPacker(pk);
		} else {
			return pk;
		}
	}

	Template[] createTemplates(List<FieldOption> fieldOpts) {
		Template[] tmpls = new Template[fieldOpts.size()];
		for (int i = 0; i < tmpls.length; ++i) {
			tmpls[i] = fieldOpts.get(i).tmpl;
		}
		return tmpls;
	}

	Template[] createTemplates(Field[] fields) {
		Template[] tmpls = new Template[fields.length];
		for (int i = 0; i < tmpls.length; ++i) {
			tmpls[i] = createTemplate(fields[i]);
		}
		return tmpls;
	}

	Template createTemplate(Field field) {
		boolean isOptional = isAnnotated(field, MessagePackOptional.class);
		Class<?> c = field.getType();
		Template tmpl = null;
		if (List.class.isAssignableFrom(c) || Map.class.isAssignableFrom(c)) {
			tmpl = createTemplate(field.getGenericType());
		} else {
			tmpl = createTemplate(c);
		}
		if (isOptional) {
			return new OptionalTemplate(tmpl);
		} else {
			return tmpl;
		}
	}

	private boolean isAnnotated(Field field, Class<? extends Annotation> with) {
		return field.getAnnotation(with) != null;
	}

	private void addPackMethod(CtClass packerCtClass, Class<?> c,
			Field[] fields, boolean isEnum) {
		// void pack(Packer pk, Object target) throws IOException;
		StringBuilder sb = new StringBuilder();
		if (!isEnum) {
			insertPackMethodBody(sb, c, fields);
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
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfPackMethodCall(sb, fields[i], i);
		}
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}

	private void insertCodeOfPackMethodCall(StringBuilder sb, Field field, int i) {
		// _$$_packers[i].pack($1, new Integer(target.fi));
		Class<?> type = field.getType();
		boolean isPrim = type.isPrimitive();
		Object[] args = new Object[] {
				i,
				isPrim ? "new " + getPrimToWrapperType(type).getName() + "("
						: "", field.getName(), isPrim ? ")" : "" };
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
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_01, args0));
		// $1.unpackArray();
		Object[] args1 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_02, args1));
		insertCodeOfUnpackMethodCalls(sb, fields);
		// return _$$_t;
		Object[] args2 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_04, args2));
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
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_03, args));
	}

	private void insertOrdinalEnumUnpackMethodBody(StringBuilder sb,
			Class<?> type) {
		// Object unpack(Unpacker u) throws IOException, MessageTypeException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		// $1.unpackArray();
		Object[] args0 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_02, args0));
		// int i = $1.unapckInt();
		Object[] args1 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_05, args1));
		// return Foo.class.getEnumConstants()[i];
		Object[] args2 = new Object[] { classToString(type) };
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_06, args2));
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
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_01, args0));
		// MessagePackObject[] _$$_ary = $1.asArray();
		Object[] args1 = new Object[] { classToString(MessagePackObject[].class) };
		sb.append(String.format(STATEMENT_TMPL_CONVERTMETHODBODY_01, args1));
		insertCodeOfConvertMethodCalls(sb, fields);
		// return _$$_t;
		Object[] args2 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_04, args2));
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
		sb.append(String.format(STATEMENT_TMPL_CONVERTMETHODBODY_02, args));
	}

	private void insertOrdinalEnumConvertMethodBody(StringBuilder sb,
			Class<?> type) {
		// Object convert(MessagePackObject mpo) throws MessageTypeException;
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		// MessagePackObject[] _$$_ary = $1.asArray();
		Object[] args0 = new Object[] { classToString(MessagePackObject[].class) };
		sb.append(String.format(STATEMENT_TMPL_CONVERTMETHODBODY_01, args0));
		// int i = _$$_ary[0].asInt();
		Object[] args1 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_CONVERTMETHODBODY_03, args1));
		// return Foo.class.getEnumConstants()[i];
		Object[] args2 = new Object[] { classToString(type) };
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_06, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}
}
