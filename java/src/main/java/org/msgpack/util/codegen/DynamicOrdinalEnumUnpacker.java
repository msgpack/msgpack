package org.msgpack.util.codegen;

import org.msgpack.MessageUnpacker;

public class DynamicOrdinalEnumUnpacker {
	public static MessageUnpacker create(Class<?> c) {
		return DynamicOrdinalEnumTemplate.create(c);
	}
}
