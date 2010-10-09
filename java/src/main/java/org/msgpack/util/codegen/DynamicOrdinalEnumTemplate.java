package org.msgpack.util.codegen;

import org.msgpack.Template;

public class DynamicOrdinalEnumTemplate {
	public static Template create(Class<?> c) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> tmplClass = gen.generateOrdinalEnumTemplateClass(c);
			return (Template) tmplClass.newInstance();
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
