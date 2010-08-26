package org.msgpack.tmp;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.lang.reflect.Field;
import java.util.HashMap;

import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;

import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class DynamicCodeGenerator {

	private static final String ENHANCED_CLASS_NAME_POSTFIX = "_$$_Enhanced";

	private static final String SPACE = " ";

	private static final String MODIFIER_PUBLIC = "public";

	private static final String METHOD_NAME_MESSAGEPACK = "messagePack";

	private static final String METHOD_NAME_MESSAGEUNPACK = "messageUnpack";

	private static final String PACKER_CLASS_TYPE_NAME = Packer.class.getName();

	private static final String VOID_TYPE_NAME = "void";

	private static final String PACKER_OBJECT_NAME = "pk";

	private static final String UNPACKER_CLASS_TYPE_NAME = Unpacker.class
			.getName();

	private static final String UNPACKER_OBJECT_NAME = "pk";

	private HashMap<String, Class<?>> classMap;

	private HashMap<String, Object> objectCacheMap;

	private ClassPool pool;

	public DynamicCodeGenerator() {
		classMap = new HashMap<String, Class<?>>();
		objectCacheMap = new HashMap<String, Object>();
		pool = ClassPool.getDefault();
	}

	public Object newEnhancedInstance(Class<?> targetClass) throws Exception {
		String targetClassName = targetClass.getName();
		// Class<?> enhancedClass = classMap.get(targetClassName);
		Object enhancedObject = objectCacheMap.get(targetClassName);
		// if (enhancedClass == null) {
		if (enhancedObject == null) {
			CtClass enhancedCtClass = createEnhancedCtClass(targetClassName);
			// System.out.println("enhanced class name: "
			// + enhancedCtClass.getName());
			addSuperclass(enhancedCtClass, targetClassName);
			addConstructor(enhancedCtClass);
			createMessagePackMethod(enhancedCtClass, targetClass);
			createMessageUnpackMethod(enhancedCtClass, targetClass);
			Class enhancedClass = loadEnhancedClass(enhancedCtClass);
			// classMap.put(targetClassName, enhancedClass);
			enhancedObject = enhancedClass.newInstance();
			objectCacheMap.put(targetClassName, enhancedObject);
		}
		// return newEnhancedInstance0(enhancedClass);
		return enhancedObject;
	}

	private CtClass createEnhancedCtClass(final String targetClassName)
			throws Exception {
		return pool.makeClass(targetClassName + ENHANCED_CLASS_NAME_POSTFIX);
	}

	private void addSuperclass(CtClass enhancedCtClass,
			final String targetClassName) throws Exception {
		CtClass targetCtClass = pool.get(targetClassName);
		enhancedCtClass.setSuperclass(targetCtClass);
	}

	private void addConstructor(CtClass enhancedCtClass) throws Exception {
		CtConstructor newCtConstructor = CtNewConstructor
				.defaultConstructor(enhancedCtClass);
		enhancedCtClass.addConstructor(newCtConstructor);
	}

	private void createMessagePackMethod(CtClass enhancedCtClass,
			Class<?> targetClass) throws Exception {
		StringBuilder sb = new StringBuilder();
		sb.append(MODIFIER_PUBLIC).append(SPACE).append(VOID_TYPE_NAME).append(
				SPACE).append(METHOD_NAME_MESSAGEPACK).append("(").append(
				PACKER_CLASS_TYPE_NAME).append(SPACE)
				.append(PACKER_OBJECT_NAME).append(")").append(SPACE).append(
						"throws").append(SPACE).append("java.io.IOException")
				.append(SPACE).append("{");
		Field[] fields = targetClass.getFields();
		sb.append(PACKER_OBJECT_NAME).append(".").append("packArray").append(
				"(").append(fields.length).append(")").append(";");
		for (Field field : fields) {
			insertCodeOfMessagePack(field, sb);
		}
		sb.append("}");
		// System.out.println("messagePack method: " + sb.toString());
		CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhancedCtClass);
		enhancedCtClass.addMethod(newCtMethod);
	}

	private void insertCodeOfMessagePack(Field field, StringBuilder sb) {
		Class<?> type = field.getType();
		if (type.equals(int.class)) {
			sb.append(PACKER_OBJECT_NAME).append(".").append("pack")
					.append("(").append(field.getName()).append(")")
					.append(";");
		} else if (type.equals(String.class)) {
			sb.append(PACKER_OBJECT_NAME).append(".").append("pack")
					.append("(").append(field.getName()).append(")")
					.append(";");
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private void createMessageUnpackMethod(CtClass enhancedCtClass,
			Class<?> targetClass) throws Exception {
		StringBuilder sb = new StringBuilder();
		sb
				.append(MODIFIER_PUBLIC)
				.append(SPACE)
				.append(VOID_TYPE_NAME)
				.append(SPACE)
				.append(METHOD_NAME_MESSAGEUNPACK)
				.append("(")
				.append(UNPACKER_CLASS_TYPE_NAME)
				.append(SPACE)
				.append(UNPACKER_OBJECT_NAME)
				.append(")")
				.append(SPACE)
				.append("throws")
				.append(SPACE)
				.append("org.msgpack.MessageTypeException, java.io.IOException")
				.append(SPACE).append("{");
		Field[] fields = targetClass.getFields();
		sb.append(UNPACKER_OBJECT_NAME).append(".").append("unpackArray()")
				.append(";");
		// TODO
		for (Field field : fields) {
			insertCodeOfMessageUnpack(field, sb);
		}
		sb.append("}");
		// System.out.println("messageUnpack method: " + sb.toString());
		CtMethod newCtMethod = CtNewMethod.make(sb.toString(), enhancedCtClass);
		enhancedCtClass.addMethod(newCtMethod);
	}

	private void insertCodeOfMessageUnpack(Field field, StringBuilder sb) {
		Class<?> type = field.getType();
		if (type.equals(int.class)) {
			sb.append(field.getName()).append(SPACE).append("=").append(SPACE)
					.append(PACKER_OBJECT_NAME).append(".").append("unpackInt")
					.append("(").append(")").append(";");
		} else if (type.equals(String.class)) {
			sb.append(field.getName()).append(SPACE).append("=").append(SPACE)
					.append(PACKER_OBJECT_NAME).append(".").append(
							"unpackString").append("(").append(")").append(";");
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private Class<?> loadEnhancedClass(CtClass enhancedCtClass)
			throws Exception {
		return enhancedCtClass.toClass(null, null);
	}

	private Object newEnhancedInstance0(Class<?> enhancedClass) {
		try {
			return enhancedClass.newInstance();
		} catch (Exception e) {
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) throws Exception {
		DynamicCodeGenerator gen = new DynamicCodeGenerator();
		Image3 src = (Image3) gen.newEnhancedInstance(Image3.class);
		src.title = "msgpack";
		src.uri = "http://msgpack.org/";
		src.width = 2560;
		src.height = 1600;
		src.size = 4096000;

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		src.messagePack(new Packer(out));
		Image3 dst = (Image3) gen.newEnhancedInstance(Image3.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		dst.messageUnpack(pac);

//		System.out.println(dst.equals(src));
	}
}
