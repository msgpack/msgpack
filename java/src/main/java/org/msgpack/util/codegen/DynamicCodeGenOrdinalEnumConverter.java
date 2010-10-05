package org.msgpack.util.codegen;

import org.msgpack.MessageConverter;

public class DynamicCodeGenOrdinalEnumConverter {
	public static MessageConverter create(Class<?> c) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> unpackerClass = gen.generateOrdinalEnumConverterClass(c);
			return (MessageConverter) unpackerClass.newInstance();
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
