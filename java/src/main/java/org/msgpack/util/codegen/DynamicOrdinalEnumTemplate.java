package org.msgpack.util.codegen;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

import org.msgpack.Template;
import org.msgpack.util.codegen.DynamicCodeGenBase.TemplateAccessor;

public class DynamicOrdinalEnumTemplate {
	public static Template create(Class<?> c) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> tmplClass = gen.generateOrdinalEnumTemplateClass(c);
			Constructor<?> cons = tmplClass
					.getDeclaredConstructor(new Class[] { Class.class });
			Object obj = cons.newInstance(new Object[] { c });
			((TemplateAccessor) obj).setTemplates(gen.getTemplates(c));
			return (Template) obj;
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (SecurityException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (NoSuchMethodException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalArgumentException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (InvocationTargetException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
