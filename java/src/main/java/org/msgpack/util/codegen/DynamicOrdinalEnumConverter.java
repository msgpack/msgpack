package org.msgpack.util.codegen;

import org.msgpack.MessageConverter;

public class DynamicOrdinalEnumConverter {
	public static MessageConverter create(Class<?> c) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> unpackerClass = gen.generateOrdinalEnumTemplateClass(c);
			return (MessageConverter) unpackerClass.newInstance();
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
