package org.msgpack.util.codegen;

import org.msgpack.MessageUnpacker;

public class DynamicCodeGenUnpacker {
	public static MessageUnpacker create(Class<?> c) {
		return DynamicCodeGenTemplate.create(c);
	}
}
