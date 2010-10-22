package org.msgpack.util.codegen;

import java.util.List;

import org.msgpack.MessagePacker;

public class DynamicPacker {

	public static MessagePacker create(Class<?> c) {
		return create(c, null);
	}

	public static MessagePacker create(Class<?> c, List<FieldOption> fieldOpts) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> packerClass = gen.generateMessagePackerClass(c, fieldOpts);
			return (MessagePacker) packerClass.newInstance();
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
