package org.msgpack.util.codegen;

import org.msgpack.MessageConverter;

public class DynamicConverter {
	public static MessageConverter create(Class<?> c) {
		return DynamicTemplate.create(c);
	}
}
