package org.msgpack.util.codegen;

import org.msgpack.MessageConverter;

public class DynamicOrdinalEnumConverter {
	public static MessageConverter create(Class<?> c) {
		return DynamicOrdinalEnumTemplate.create(c);
	}
}
