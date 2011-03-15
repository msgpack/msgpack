package org.msgpack.template.builder;

import java.lang.annotation.Annotation;
import java.lang.reflect.Type;

import org.msgpack.annotation.MessagePackBeans;
import org.msgpack.annotation.MessagePackMessage;

public class MessagePackBeansTemplateSelector implements BuilderSelector{
	
	public static final String NAME = "MessagePackBeansTemplateBuilder";
	
	
    TemplateBuilder builder;
	public MessagePackBeansTemplateSelector(TemplateBuilder builder){
		this.builder = builder;
	}
	
	
	public String getName(){
		return NAME;
	}
	
	@Override
	public boolean matchType(Type targetType) {
		Class<?> target = (Class<?>)targetType;
		return isAnnotated(target, MessagePackBeans.class);
	}

	@Override
	public TemplateBuilder getTemplateBuilder(Type targetType) {
		return builder;
	}
	

	private boolean isAnnotated(Class<?> ao, Class<? extends Annotation> with) {
		return ao.getAnnotation(with) != null;
	}

}
