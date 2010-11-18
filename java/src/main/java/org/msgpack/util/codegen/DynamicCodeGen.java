//
// MessagePack for Java
//
// Copyright (C) 2009-2010 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
package org.msgpack.util.codegen;

import java.io.IOException;
import java.lang.annotation.Annotation;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import javassist.CannotCompileException;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.CtNewMethod;
import javassist.NotFoundException;

import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.Optional;
import org.msgpack.annotation.Nullable;
import org.msgpack.template.OptionalTemplate;
import org.msgpack.template.NullableTemplate;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class DynamicCodeGen extends DynamicCodeGenBase implements Constants {

	private static Logger LOG = LoggerFactory.getLogger(DynamicCodeGen.class);

	private static DynamicCodeGen INSTANCE;

	public static DynamicCodeGen getInstance() {
		return getInstance(null);

	}

	public static DynamicCodeGen getInstance(ClassLoader cl) {
		if (INSTANCE == null) {
			LOG.info("create an instance of the type: "
					+ DynamicCodeGen.class.getName());
			INSTANCE = new DynamicCodeGen();
			if (cl != null) {
				INSTANCE.setClassLoader(cl);
			}
		}
		return INSTANCE;		
	}
	
	private ConcurrentHashMap<String, Template[]> tmplCache;

	DynamicCodeGen() {
		super();
		tmplCache = new ConcurrentHashMap<String, Template[]>();
	}

	public void setTemplates(Class<?> type, Template[] tmpls) {
		tmplCache.put(type.getName(), tmpls);
	}

	public Template[] getTemplates(Class<?> type) {
		return tmplCache.get(type.getName());
	}

	public Class<?> generateTemplateClass(Class<?> origClass,
			FieldList fieldList) {
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
			if (fieldList != null) {
				tmpls = createTemplates(fields, fieldList);
			} else {
				tmpls = createTemplates(fields);
			}
			setTemplates(origClass, tmpls);
			addPackMethod(tmplCtClass, origClass, fields, false);
			addUnpackMethod(tmplCtClass, origClass, fields, false);
			addConvertMethod(tmplCtClass, origClass, fields, false);
			Class<?> tmplClass = createClass(tmplCtClass);
			LOG.debug("generated a template class for " + origClass.getName());
			return tmplClass;
		} catch (NotFoundException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e.getMessage(), e);
			LOG.error(ex.getMessage(), ex);
			throw ex;
		} catch (CannotCompileException e) {
			DynamicCodeGenException ex = new DynamicCodeGenException(e.getMessage(), e);
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
			addPackMethod(tmplCtClass, origClass, null, true);
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

	Field[] sortFields(Field[] fields, FieldList fieldList) {
		List<FieldList.Entry> list = fieldList.getList();
		if (fields.length != list.size()) {
			throwFieldSortingException(String.format(
					"Mismatch: public field num: %d, option num: %d",
					new Object[] { fields.length, list.size() }));
		}
		Field[] sorted = new Field[fields.length];
		for (int i = 0; i < sorted.length; ++i) {
			FieldList.Entry e = list.get(i);
			Field match = null;
			for (Field f : fields) {
				if (e.getName().equals(f.getName())) {
					match = f;
					break;
				}
			}
			if (match != null) {
				sorted[i] = match;
			} else {
				throwFieldSortingException(String.format(
						"Mismatch: a %s field option is not declared",
						new Object[] { e.getName() }));
			}
		}
		return sorted;
	}

	Template[] createTemplates(Field[] fields, FieldList fieldList) {
		List<FieldList.Entry> list = fieldList.getList();
		//if (fields.length != list.size()) {
		//	throwFieldSortingException(String.format(
		//			"Mismatch: public field num: %d, option num: %d",
		//			new Object[] { fields.length, list.size() }));
		//}
		Template[] tmpls = new Template[list.size()];
		for(int i = 0; i < list.size(); ++i) {
			FieldList.Entry e = list.get(i);
			Field match = null;
			// FIXME if(!e.isAvailable())
			for (Field f : fields) {
				if (e.getName().equals(f.getName())) {
					match = f;
					break;
				}
			}
			if (match == null) {
				throwFieldSortingException(String.format(
						"Mismatch: a %s field option is not declared",
						new Object[] { e.getName() }));
			}
			Template tmpl = createTemplate(match);
			if(e.isOptional()) {
				tmpl = new OptionalTemplate(tmpl);
			} else if(e.isNullable()) {
				tmpl = new NullableTemplate(tmpl);
			}
			tmpls[i] = tmpl;
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
		Class<?> c = field.getType();
		Template tmpl = null;
		if (List.class.isAssignableFrom(c) || Map.class.isAssignableFrom(c)
				|| Collection.class.isAssignableFrom(c)) {
			tmpl = createTemplate(field.getGenericType());
		} else {
			tmpl = createTemplate(c);
		}
		if (isAnnotated(field, Optional.class)) {
			// @Optional types
			return new OptionalTemplate(tmpl);
		}
		if (!c.isPrimitive() && isAnnotated(field, Nullable.class)) {
			// @Nullable reference types
			return new NullableTemplate(tmpl);
		}
		return tmpl;
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
			CtClass[] paramTypes = new CtClass[] { classToCtClass(Unpacker.class), classToCtClass(Object.class) };
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
		Object[] args0 = new Object[] { typeName, typeName, typeName };
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_01, args0));
		// int _$$_L = $1.unpackArray();
		Object[] args1 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_02, args1));
		insertCodeOfUnpackMethodCalls(sb, fields, getTemplates(type));
		// return _$$_t;
		Object[] args2 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_04, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}

	private void insertCodeOfUnpackMethodCalls(StringBuilder sb, Field[] fields,
			Template[] tmpls) {
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfUnpackMethodCall(sb, fields[i], i, tmpls[i]);
		}
		insertCodeOfUnpackTrails(sb, fields.length);
	}

	private void insertCodeOfUnpackMethodCall(StringBuilder sb, Field field,
			int i, Template tmpl) {
		// target.fi = ((Integer)_$$_tmpls[i].unpack(_$$_pk)).intValue();
		Class<?> returnType = field.getType();
		boolean isPrim = returnType.isPrimitive();
		String callExpr;
		if(isPrim) {
			Object[] args = new Object[] {
				field.getName(),
					"(",
					getPrimToWrapperType(returnType).getName(),
					i,
					")." + getPrimTypeValueMethodName(returnType) + "()" };
			callExpr = String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_03_NULL, args);
		} else {
			Object[] args = new Object[] {
				field.getName(),
					"",
					classToString(returnType),
					i,
					field.getName(),
					"" };
			callExpr = String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_03, args);
		}
		if (tmpl instanceof OptionalTemplate) {
			Object[] args0 = new Object[] { i, callExpr };
			// if (_$$_len > i && !unpacker.tryUnpackNull()) { ... }
			sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_08, args0));
		} else {
			// if (_$$_len <= i) { throw new MessageTypeException(); }
			Object[] args0 = new Object[] { i };
			sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_07, args0));
			sb.append(callExpr);
		}
	}

	private void insertCodeOfUnpackTrails(StringBuilder sb, int len) {
		// for (int _$$_i = len; _$$_i < _$$_len; _$$_i++) { $1.unpackObject(); }
		Object[] args0 = new Object[] { len };
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_09, args0));
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
			CtClass[] paramTypes = new CtClass[] { classToCtClass(MessagePackObject.class), classToCtClass(Object.class) };
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
		Object[] args0 = new Object[] { typeName, typeName, typeName };
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_01, args0));
		// MessagePackObject[] _$$_ary = $1.asArray();
		Object[] args1 = new Object[] { classToString(MessagePackObject[].class) };
		sb.append(String.format(STATEMENT_TMPL_CONVERTMETHODBODY_01, args1));
		sb.append(STATEMENT_TMPL_CONVERTMETHODBODY_04);
		Template[] tmpls = getTemplates(type);
		insertCodeOfConvertMethodCalls(sb, fields, tmpls);
		// return _$$_t;
		Object[] args2 = new Object[0];
		sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_04, args2));
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
	}

	private void insertCodeOfConvertMethodCalls(StringBuilder sb, Field[] fields,
			Template[] tmpls) {
		for (int i = 0; i < fields.length; ++i) {
			insertCodeOfConvMethodCall(sb, fields[i], i, tmpls[i]);
		}
	}

	private void insertCodeOfConvMethodCall(StringBuilder sb, Field field,
			int i, Template tmpl) {
		// target.fi = ((Object)_$$_tmpls[i].convert(_$$_ary[i])).intValue();
		Class<?> returnType = field.getType();
		boolean isPrim = returnType.isPrimitive();
		String callExpr;
		if(isPrim) {
			Object[] args = new Object[] {
				field.getName(),
					"(",
					getPrimToWrapperType(returnType).getName(),
					i,
					i,
					")." + getPrimTypeValueMethodName(returnType) + "()" };
			callExpr = String.format(STATEMENT_TMPL_CONVERTMETHODBODY_02_NULL, args);
		} else {
			Object[] args = new Object[] {
				field.getName(),
					"",
					classToString(returnType),
					i,
					i,
					field.getName(),
					"" };
			callExpr = String.format(STATEMENT_TMPL_CONVERTMETHODBODY_02, args);
		}
		if (tmpl instanceof OptionalTemplate) {
			Object[] args0 = new Object[] { i, i, callExpr };
			// if (_$$_len > i && !_$$_ary[i].isNull()) { ... }
			sb.append(String.format(STATEMENT_TMPL_CONVERTMETHODBODY_05, args0));
		} else {
			// if (_$$_len <= i) { throw new MessageTypeException(); }
			Object[] args0 = new Object[] { i };
			sb.append(String.format(STATEMENT_TMPL_UNPACKERMETHODBODY_07, args0));
			sb.append(callExpr);
		}
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
