package org.msgpack.template.builder;

import java.lang.reflect.Type;

import org.msgpack.Template;
import org.msgpack.template.FieldList;
import org.msgpack.template.FieldOption;
import org.msgpack.template.IFieldEntry;
import org.msgpack.template.IFieldEntryReader;
import org.msgpack.template.TemplateBuildException;
import org.msgpack.template.javassist.BuildContextFactory;

public abstract class CustomTemplateBuilder extends TemplateBuilder {


	public abstract IFieldEntryReader getFieldEntryReader();

	
	public abstract Template buildTemplate(Class<?> targetClass , IFieldEntry[] entries);
	
	public Template buildTemplate(Class<?> targetClass ,FieldOption implicitOption ){
		checkValidation(targetClass);
		return buildTemplate(targetClass,
				getFieldEntryReader().readFieldEntries(targetClass, implicitOption));
	}
	public Template buildTemplate(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
		checkValidation(targetClass);
		return buildTemplate(targetClass, getFieldEntryReader().convertFieldEntries(targetClass, flist));
	}

	@Override
	public Template buildTemplate(Type targetType) {
		Class<?> targetClass = (Class<?>)targetType;
		IFieldEntryReader reader = getFieldEntryReader();
		FieldOption implicitOption = reader.readImplicitFieldOption(targetClass);
		checkValidation(targetClass);
		
		IFieldEntry[] entries = reader.readFieldEntries(targetClass, implicitOption);
		
		return buildTemplate(targetClass,entries);
	}
	private void checkValidation(Class<?> targetClass) {
		if(targetClass.isInterface()) {
			throw new TemplateBuildException("cannot build template of interface");
		}
		if(targetClass.isArray()) {
			throw new TemplateBuildException("cannot build template of array class");
		}
		if(targetClass.isPrimitive()) {
			throw new TemplateBuildException("cannot build template of primitive type");
		}
	}
}