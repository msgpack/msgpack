package org.msgpack.util.codegen;

import java.util.List;

import org.msgpack.Template;
import org.msgpack.util.codegen.DynamicCodeGenBase.TemplateAccessor;

public class DynamicTemplate {
	public static Template create(Class<?> c) {
		return create(c, null);
	}

	public static Template create(Class<?> c, List<FieldOption> fieldOpts) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> tmplClass = gen.generateTemplateClass(c, fieldOpts);
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
