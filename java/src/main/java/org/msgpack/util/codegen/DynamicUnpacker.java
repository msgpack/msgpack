package org.msgpack.util.codegen;

import org.msgpack.MessageUnpacker;

public class DynamicUnpacker {
	public static MessageUnpacker create(Class<?> c) {
		return DynamicTemplate.create(c);
	}
}
