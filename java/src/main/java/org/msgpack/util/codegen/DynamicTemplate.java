package org.msgpack.util.codegen;

import org.msgpack.Template;
import org.msgpack.util.codegen.DynamicCodeGenBase.TemplateAccessor;

public class DynamicTemplate {
	public static Template create(Class<?> c) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> tmplClass = gen.generateTemplateClass(c);
			Object obj = tmplClass.newInstance();
			((TemplateAccessor) obj).setTemplates(gen.getTemplates(c));
			return (Template) obj;
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
