package org.msgpack.util.codegen;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.List;

import org.msgpack.MessagePacker;
import org.msgpack.util.codegen.DynamicCodeGenBase.MessagePackerAccessor;

public class DynamicPacker {

	public static MessagePacker create(Class<?> c) {
		return create(c, null);
	}

	public static MessagePacker create(Class<?> c, List<FieldOption> fieldOpts) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> packerClass = gen.generateMessagePackerClass(c, fieldOpts);
			Constructor<?> cons = packerClass
					.getDeclaredConstructor(new Class[] { Class.class });
			Object obj = cons.newInstance(new Object[] { c });
			((MessagePackerAccessor) obj).setMessagePackers(gen
					.getMessagePackers(c));
			return (MessagePacker) obj;
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (SecurityException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (NoSuchMethodException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalArgumentException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (InvocationTargetException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
