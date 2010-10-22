package org.msgpack.util.codegen;

import java.util.List;

import org.msgpack.MessageConverter;

public class DynamicConverter {
	public static MessageConverter create(Class<?> c) {
		return create(c, null);
	}

	public static MessageConverter create(Class<?> c,
			List<FieldOption> fieldOpts) {
		return DynamicTemplate.create(c, fieldOpts);
	}
}
