package org.msgpack.template.builder;

import java.lang.reflect.Type;

/**
 * Match condition for TemplateBuilder.
 * @author takeshita
 *
 */
public interface BuilderSelector {
	
	
	/**
	 * Name of this.
	 * @return
	 */
	public String getName();
	
	
	public abstract boolean matchType(Type targetType);
	
	
	public abstract TemplateBuilder getTemplateBuilder(Type targetType);
	
	

}
