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

import java.io.IOException;
import java.lang.reflect.*;
import java.lang.annotation.*;
import java.util.List;
import java.util.ArrayList;
import java.util.EnumSet;
import org.msgpack.*;
import org.msgpack.annotation.*;

public class FieldEntry implements IFieldEntry {
	private Field field;
	private FieldOption option;

	public FieldEntry() {
		this.field = null;
		this.option = FieldOption.IGNORE;
	}

	public FieldEntry(FieldEntry e) {
		this.field = e.field;
		this.option = e.option;
	}

	public FieldEntry(Field field, FieldOption option) {
		this.field = field;
		this.option = option;
	}

	public Field getField() {
		return field;
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#getName()
	 */
	@Override
	public String getName() {
		return field.getName();
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#getType()
	 */
	@Override
	public Class<?> getType() {
		return field.getType();
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#getJavaTypeName()
	 */
	@Override
	public String getJavaTypeName() {
		Class<?> type = field.getType();
		if(type.isArray()) {
			return arrayTypeToString(type);
		} else {
			return type.getName();
		}
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#getGenericType()
	 */
	@Override
	public Type getGenericType() {
		return field.getGenericType();
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#getOption()
	 */
	@Override
	public FieldOption getOption() {
		return option;
	}

	/* (non-Javadoc)
	 * @see org.msgpack.template.IFieldEntry#isAvailable()
	 */
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
}