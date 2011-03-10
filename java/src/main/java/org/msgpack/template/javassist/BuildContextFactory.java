package org.msgpack.template.javassist;

import org.msgpack.template.JavassistTemplateBuilder;

public interface BuildContextFactory {
	
	public BuildContextBase createBuildContext(JavassistTemplateBuilder builder);

}
