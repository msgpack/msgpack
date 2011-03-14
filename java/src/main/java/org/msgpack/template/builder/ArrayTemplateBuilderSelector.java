package org.msgpack.template.builder;

import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Type;

import org.msgpack.Template;

public class ArrayTemplateBuilderSelector implements BuilderSelector {

	public static final String NAME = "ArrayTemplateBuilder";
	
	@Override
	public String getName(){
		return NAME;
	}
	
	
	@Override
	public boolean matchType(Type targetType) {
		if(targetType instanceof GenericArrayType){
			return true;
		}
		Class<?> targetClass = (Class<?>)targetType;
		return targetClass.isArray();
	}
	
	ArrayTemplateBuilder templateBuilder = new ArrayTemplateBuilder();

	@Override
	public TemplateBuilder getTemplateBuilder(Type target) {
		return templateBuilder;
	}


}
