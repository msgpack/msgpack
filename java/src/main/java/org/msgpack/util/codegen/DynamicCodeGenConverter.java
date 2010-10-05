package org.msgpack.util.codegen;

import org.msgpack.MessageConverter;

public class DynamicCodeGenConverter {
	public static MessageConverter create(Class<?> c) {
		return DynamicCodeGenTemplate.create(c);
	}
}
