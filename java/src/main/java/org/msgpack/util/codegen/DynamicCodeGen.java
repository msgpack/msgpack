package org.msgpack.util.codegen;

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.NotFoundException;

import org.msgpack.MessagePacker;
import org.msgpack.Packer;
import org.msgpack.Template;

public class DynamicCodeGen extends DynamicCodeGenBase implements Constants {

	private static DynamicCodeGen INSTANCE;

	private static AtomicInteger COUNTER;

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
			String packerName = origName + POSTFIX_TYPE_NAME_PACKER;
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

	public Class<?> generateTemplateClass(Class<?> origClass) {
		try {
			String origName = origClass.getName();
			String packerName = origName + POSTFIX_TYPE_NAME_PACKER;
			checkClassValidation(origClass);
			checkDefaultConstructorValidation(origClass);
			CtClass packerCtClass = pool.makeClass(packerName);
			setInterface(packerCtClass, Template.class);
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
		sb.append(KEYWORD_MODIFIER_PUBLIC);
		sb.append(CHAR_NAME_SPACE);
		sb.append(void.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(METHOD_NAME_PACK);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(Packer.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_PK);
		sb.append(CHAR_NAME_COMMA);
		sb.append(CHAR_NAME_SPACE);
		sb.append(Object.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(VARIABLE_NAME_OBJ);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SPACE);
		sb.append(KEYWORD_THROWS);
		sb.append(CHAR_NAME_SPACE);
		sb.append(IOException.class.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		insertPackMethodBody(sb, c, fs);
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		// System.out.println("pack method: " + sb.toString());
		CtMethod newCtMethod = CtNewMethod.make(sb.toString(), packerCtClass);
		packerCtClass.addMethod(newCtMethod);
	}

	private void insertPackMethodBody(StringBuilder sb, Class<?> c, Field[] fs) {
		insertLocalVariableDecl(sb, c, VARIABLE_NAME_TARGET);
		StringBuilder mc = new StringBuilder();
		insertTypeCast(mc, c, VARIABLE_NAME_OBJ);
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

	private Class<?> createClass(CtClass packerCtClass)
			throws CannotCompileException {
		return packerCtClass.toClass(null, null);
	}
}
