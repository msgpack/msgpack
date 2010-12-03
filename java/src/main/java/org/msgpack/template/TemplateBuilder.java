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

public abstract class TemplateBuilder {
	public static class FieldEntry {
		private Field field = null;
		private FieldOption option = FieldOption.IGNORE;

		public FieldEntry() {
		}

		public FieldEntry(Field field, FieldOption option) {
			this.field = field;
			this.option = option;
		}

		public Field getField() {
			return field;
		}

		public String getName() {
			return field.getName();
		}

		public Class<?> getType() {
			return field.getType();
		}

		public String getJavaTypeName() {
			Class<?> type = field.getType();
			if(type.isArray()) {
				return arrayTypeToString(type);
			} else {
				return type.getName();
			}
		}

		public Type getGenericType() {
			return field.getGenericType();
		}

		public FieldOption getOption() {
			return option;
		}

		public boolean isAvailable() {
			return option != FieldOption.IGNORE;
		}

		public boolean isRequired() {
			return option == FieldOption.REQUIRED;
		}

		public boolean isOptional() {
			return option == FieldOption.OPTIONAL;
		}

		public boolean isNullable() {
			return option == FieldOption.NULLABLE;
		}

		public boolean isAnnotated(Class<? extends Annotation> with) {
			return field.getAnnotation(with) != null;
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

	// Override this method
	public abstract Template buildTemplate(Class<?> targetClass, FieldEntry[] entries);

	// Override this method
	public abstract Template buildOrdinalEnumTemplate(Class<?> targetClass, Enum<?>[] entries);


	public Template buildTemplate(Class<?> targetClass) {
		checkTypeValidation(targetClass);
		return buildTemplate(targetClass, readFieldEntries(targetClass));
	}

	public Template buildTemplate(Class<?> targetClass, FieldOption implicitOption) {
		checkTypeValidation(targetClass);
		return buildTemplate(targetClass, readFieldEntries(targetClass, implicitOption));
	}

	public Template buildTemplate(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
		checkTypeValidation(targetClass);
		return buildTemplate(targetClass, convertFieldEntries(targetClass, flist));
	}

	public Template buildOrdinalEnumTemplate(Class<?> targetClass) {
		checkOrdinalEnumValidation(targetClass);
		Enum<?>[] entries = (Enum<?>[])targetClass.getEnumConstants();
		return buildOrdinalEnumTemplate(targetClass, entries);
	}


	private static TemplateBuilder instance;
	static {
		instance = selectDefaultTemplateBuilder();
	}

	private static TemplateBuilder selectDefaultTemplateBuilder() {
		try {
			// FIXME JavassistTemplateBuilder doesn't work on DalvikVM
			if(System.getProperty("java.vm.name").equals("Dalvik")) {
				return ReflectionTemplateBuilder.getInstance();
			}
		} catch (Exception e) {
		}
		return JavassistTemplateBuilder.getInstance();
	}

	synchronized static void setInstance(TemplateBuilder builder) {
		instance = builder;
	}

	public static Template build(Class<?> targetClass) {
		return instance.buildTemplate(targetClass);
	}

	public static Template build(Class<?> targetClass, FieldOption implicitOption) {
		return instance.buildTemplate(targetClass, implicitOption);
	}

	public static Template build(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
		return instance.buildTemplate(targetClass, flist);
	}

	public static Template buildOrdinalEnum(Class<?> targetClass) {
		return instance.buildOrdinalEnumTemplate(targetClass);
	}


	protected void checkTypeValidation(Class<?> targetClass) {
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

	protected void checkOrdinalEnumValidation(Class<?> targetClass) {
		if(!targetClass.isEnum()) {
			throw new TemplateBuildException("tried to build ordinal enum template of non-enum class");
		}
	}


	protected FieldEntry[] convertFieldEntries(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
		List<FieldList.Entry> src = flist.getList();
		FieldEntry[] result = new FieldEntry[src.size()];
		for(int i=0; i < src.size(); i++) {
			FieldList.Entry s = src.get(i);
			if(s.isAvailable()) {
				result[i] = new FieldEntry(targetClass.getDeclaredField(s.getName()), s.getOption());
			} else {
				result[i] = new FieldEntry();
			}
		}
		return result;
	}

	protected FieldEntry[] readFieldEntries(Class<?> targetClass) {
		FieldOption implicitOption = readImplicitFieldOption(targetClass);
		return readFieldEntries(targetClass, implicitOption);
	}

	protected FieldEntry[] readFieldEntries(Class<?> targetClass, FieldOption implicitOption) {
		Field[] allFields = readAllFields(targetClass);

		/* index:
		 *   @Index(0) int field_a;   // 0
		 *             int field_b;   // 1
		 *   @Index(3) int field_c;   // 3
		 *             int field_d;   // 4
		 *   @Index(2) int field_e;   // 2
		 *             int field_f;   // 5
		 */
		List<FieldEntry> indexed = new ArrayList<FieldEntry>();
		int maxIndex = -1;
		for(Field f : allFields) {
			FieldOption opt = readFieldOption(f, implicitOption);
			if(opt == FieldOption.IGNORE) {
				// skip
				continue;
			}

			int index = readFieldIndex(f, maxIndex);

			if(indexed.size() > index && indexed.get(index) != null) {
				throw new TemplateBuildException("duplicated index: "+index);
			}
			if(index < 0) {
				throw new TemplateBuildException("invalid index: "+index);
			}

			while(indexed.size() <= index) {
				indexed.add(null);
			}
			indexed.set(index, new FieldEntry(f, opt));

			if(maxIndex < index) {
				maxIndex = index;
			}
		}

		FieldEntry[] result = new FieldEntry[maxIndex+1];
		for(int i=0; i < indexed.size(); i++) {
			FieldEntry e = indexed.get(i);
			if(e == null) {
				result[i] = new FieldEntry();
			} else {
				result[i] = new FieldEntry(e.getField(), e.getOption());
			}
		}

		return result;
	}

	private Field[] readAllFields(Class<?> targetClass) {
		// order: [fields of super class, ..., fields of this class]
		List<Field[]> succ = new ArrayList<Field[]>();
		int total = 0;
		for(Class<?> c = targetClass; c != Object.class; c = c.getSuperclass()) {
			Field[] fields = c.getDeclaredFields();
			total += fields.length;
			succ.add(fields);
		}
		Field[] result = new Field[total];
		int off = 0;
		for(int i=succ.size()-1; i >= 0; i--) {
			Field[] fields = succ.get(i);
			System.arraycopy(fields, 0, result, off, fields.length);
			off += fields.length;
		}
		return result;
	}

	private FieldOption readImplicitFieldOption(Class<?> targetClass) {
		MessagePackMessage a = targetClass.getAnnotation(MessagePackMessage.class);
		if(a == null) {
			return FieldOption.DEFAULT;
		}
		return a.value();
	}

	private FieldOption readFieldOption(Field field, FieldOption implicitOption) {
		int mod = field.getModifiers();
		if(Modifier.isStatic(mod) || Modifier.isFinal(mod)) {
			return FieldOption.IGNORE;
		}

		if(isAnnotated(field, Ignore.class)) {
			return FieldOption.IGNORE;
		} else if(isAnnotated(field, Required.class)) {
			return FieldOption.REQUIRED;
		} else if(isAnnotated(field, Optional.class)) {
			return FieldOption.OPTIONAL;
		} else if(isAnnotated(field, Nullable.class)) {
			if(field.getDeclaringClass().isPrimitive()) {
				return FieldOption.REQUIRED;
			} else {
				return FieldOption.NULLABLE;
			}
		}

		if(implicitOption != FieldOption.DEFAULT) {
			return implicitOption;
		}

		// default mode:
		//   transient : Ignore
		//   public    : Required
		//   others    : Ignore
		if(Modifier.isTransient(mod)) {
			return FieldOption.IGNORE;
		} else if(Modifier.isPublic(mod)) {
			return FieldOption.REQUIRED;
		} else {
			return FieldOption.IGNORE;
		}
	}

	private int readFieldIndex(Field field, int maxIndex) {
		Index a = field.getAnnotation(Index.class);
		if(a == null) {
			return maxIndex + 1;
		} else {
			return a.value();
		}
	}

	protected boolean isAnnotated(AccessibleObject ao, Class<? extends Annotation> with) {
		return ao.getAnnotation(with) != null;
	}
}

