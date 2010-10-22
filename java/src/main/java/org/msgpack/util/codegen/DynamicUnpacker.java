package org.msgpack.util.codegen;

import java.util.List;

import org.msgpack.MessageUnpacker;

public class DynamicUnpacker {
	public static MessageUnpacker create(Class<?> c) {
		return create(c, null);
	}

	public static MessageUnpacker create(Class<?> c, List<FieldOption> fieldOpts) {
		return DynamicTemplate.create(c, fieldOpts);
	}
}
