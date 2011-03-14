package org.msgpack.template.builder;

import java.lang.reflect.Type;


public interface BuilderSelector {
	
	
	
	public String getName();
	
	
	public abstract boolean matchType(Type targetType);
	
	
	public abstract TemplateBuilder getTemplateBuilder(Type targetType);
	
	

}
