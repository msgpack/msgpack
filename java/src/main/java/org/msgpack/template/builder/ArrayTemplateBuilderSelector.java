//
// MessagePack for Java
//
// Copyright (C) 2009-2011 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
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
