package org.msgpack.template.builder;

import java.lang.annotation.Annotation;
import java.lang.reflect.Type;

import org.msgpack.annotation.MessagePackOrdinalEnum;

public class MessagePackOrdinalEnumBuilderSelector implements BuilderSelector {

	public static final String NAME = "MessagePackOrdinalEnumBuilderTemplate";
	
	public String getName(){
		return NAME;
	}
	
	@Override
	public boolean matchType(Type targetType) {
		Class<?> target = (Class<?>)targetType;
		return isAnnotated(target, MessagePackOrdinalEnum.class);
	}
	
	OrdinalEnumTemplateBuilder builder = new OrdinalEnumTemplateBuilder();

	@Override
	public TemplateBuilder getTemplateBuilder(Type targetType) {
		return builder;
	}
	

	private boolean isAnnotated(Class<?> ao, Class<? extends Annotation> with) {
		return ao.getAnnotation(with) != null;
	}

}
