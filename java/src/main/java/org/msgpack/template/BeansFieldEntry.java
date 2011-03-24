//
// MessagePack for Java
//
// Copyright (C) 2009-2010 FURUHASHI Sadayuki
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
package org.msgpack.template;

import java.beans.PropertyDescriptor;
import java.io.IOException;
import java.lang.reflect.*;
import java.lang.annotation.*;
import java.util.List;
import java.util.ArrayList;
import java.util.EnumSet;
import org.msgpack.*;
import org.msgpack.annotation.*;

public class BeansFieldEntry implements IFieldEntry {

	PropertyDescriptor desc;
	FieldOption option = FieldOption.DEFAULT;
	
	public BeansFieldEntry(PropertyDescriptor desc) {
		this.desc = desc;
	}

	@Override
	public String getName() {
		return desc.getDisplayName();
	}
	public String getGetterName(){
		return desc.getReadMethod().getName();
	}
	public String getSetterName(){
		return desc.getWriteMethod().getName();
	}

	@Override
	public Class<?> getType() {
		return desc.getPropertyType();
	}

	@Override
	public String getJavaTypeName() {
		Class<?> type = getType();
		if(type.isArray()) {
			return arrayTypeToString(type);
		} else {
			return type.getName();
		}
	}
	static String arrayTypeToString(Class<?> type) {
		int dim = 1;
		Class<?> baseType = type.getComponentType();
		while(baseType.isArray()) {
			baseType = baseType.getComponentType();
			dim += 1;
		}
		StringBuilder sb = new StringBuilder();
		sb.append(baseType.getName());
		for (int i = 0; i < dim; ++i) {
			sb.append("[]");
		}
		return sb.toString();
	}

	@Override
	public Type getGenericType() {
		return desc.getReadMethod().getGenericReturnType();
	}

	@Override
	public FieldOption getOption() {
		return option;
	}
	public void setOption(FieldOption option){
		this.option = option;
	}

	@Override
	public boolean isAvailable() {
		return option != FieldOption.IGNORE;
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#isRequired()
	 */
	@Override
	public boolean isRequired() {
		return option == FieldOption.REQUIRED;
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#isOptional()
	 */
	@Override
	public boolean isOptional() {
		return option == FieldOption.OPTIONAL;
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#isNullable()
	 */
	@Override
	public boolean isNullable() {
		return option == FieldOption.NULLABLE;
	}
	
	public Object get(Object target){
		try {
			return desc.getReadMethod().invoke(target);
		} catch (IllegalArgumentException e) {
			throw new MessageTypeException(e);
		} catch (IllegalAccessException e) {
			throw new MessageTypeException(e);
		} catch (InvocationTargetException e) {
			throw new MessageTypeException(e);
		}
	}
	public void set(Object target , Object value){
		try {
			desc.getWriteMethod().invoke(target, value);
		} catch (IllegalArgumentException e) {
			throw new MessageTypeException(e);
		} catch (IllegalAccessException e) {
			throw new MessageTypeException(e);
		} catch (InvocationTargetException e) {
			throw new MessageTypeException(e);
		}
	}
	
}