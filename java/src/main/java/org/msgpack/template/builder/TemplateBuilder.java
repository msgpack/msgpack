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
package org.msgpack.template.builder;

import java.io.IOException;
import java.lang.reflect.*;
import java.lang.annotation.*;
import java.util.List;
import java.util.ArrayList;
import java.util.EnumSet;
import org.msgpack.*;
import org.msgpack.annotation.*;
import org.msgpack.template.FieldList;
import org.msgpack.template.FieldOption;
import org.msgpack.template.IFieldEntry;
import org.msgpack.template.IFieldEntryReader;
import org.msgpack.template.JavassistTemplateBuilder;
import org.msgpack.template.ReflectionTemplateBuilder;

public abstract class TemplateBuilder {

	public abstract Template buildTemplate(Type targetType);
	/*
	// Override this method
	public abstract Template buildTemplate(Class<?> targetClass, IFieldEntry[] entries);

	// Override this method
	public abstract Template buildOrdinalEnumTemplate(Class<?> targetClass, Enum<?>[] entries);

	// Override this method
	public abstract Template buildArrayTemplate(Type arrayType, Type genericBaseType, Class<?> baseClass, int dim);
    
	public abstract IFieldEntryReader getFieldEntryReader();

	public Template buildTemplate(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
		checkValidation(targetClass);
		return buildTemplate(targetClass, getFieldEntryReader().convertFieldEntries(targetClass, flist));
	}

	public Template buildTemplate(Class<?> targetClass, FieldOption implicitOption) {
		checkValidation(targetClass);
		return buildTemplate(targetClass, getFieldEntryReader().readFieldEntries(targetClass, implicitOption));
	}

	public Template buildTemplate(Class<?> targetClass) {
		FieldOption implicitOption = getFieldEntryReader().readImplicitFieldOption(targetClass);
		return buildTemplate(targetClass, implicitOption);
	}

	public Template buildOrdinalEnumTemplate(Class<?> targetClass) {
		checkOrdinalEnumValidation(targetClass);
		Enum<?>[] entries = (Enum<?>[])targetClass.getEnumConstants();
		return buildOrdinalEnumTemplate(targetClass, entries);
	}

	public Template buildArrayTemplate(Type arrayType) {
		Type baseType;
		Class<?> baseClass;
		int dim = 1;
		if(arrayType instanceof GenericArrayType) {
			GenericArrayType type = (GenericArrayType)arrayType;
			baseType = type.getGenericComponentType();
			while(baseType instanceof GenericArrayType) {
				baseType = ((GenericArrayType)baseType).getGenericComponentType();
				dim += 1;
			}
			if(baseType instanceof ParameterizedType) {
				baseClass = (Class<?>)((ParameterizedType)baseType).getRawType();
			} else {
				baseClass = (Class<?>)baseType;
			}
		} else {
			Class<?> type = (Class<?>)arrayType;
			baseClass = type.getComponentType();
			while(baseClass.isArray()) {
				baseClass = baseClass.getComponentType();
				dim += 1;
			}
			baseType = baseClass;
		}
		return buildArrayTemplate(arrayType, baseType, baseClass, dim);
	}

	private static Type getComponentType(Type arrayType) {
		if(arrayType instanceof GenericArrayType) {
			return ((GenericArrayType)arrayType).getGenericComponentType();
		} else {
			return ((Class<?>)arrayType).getComponentType();
		}
	}
	private void checkValidation(Class<?> targetClass) {
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
	private void checkOrdinalEnumValidation(Class<?> targetClass) {
		if(!targetClass.isEnum()) {
			throw new TemplateBuildException("tried to build ordinal enum template of non-enum class");
		}
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

	public synchronized static void setInstance(TemplateBuilder builder) {
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

	public static Template buildArray(Type arrayType) {
		return instance.buildArrayTemplate(arrayType);
	}*/

    /*
	private static void checkValidation(Class<?> targetClass) {
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

	private static void checkOrdinalEnumValidation(Class<?> targetClass) {
		if(!targetClass.isEnum()) {
			throw new TemplateBuildException("tried to build ordinal enum template of non-enum class");
		}
	}*/

    /*
	static IFieldEntry[] convertFieldEntries(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
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
	}*/
    
	/*static IFieldEntry[] readFieldEntries(Class<?> targetClass, FieldOption implicitOption) {
		Field[] allFields = readAllFields(targetClass);

		/* index:
		 *   @Index(0) int field_a;   // 0
		 *             int field_b;   // 1
		 *   @Index(3) int field_c;   // 3
		 *             int field_d;   // 4
		 *   @Index(2) int field_e;   // 2
		 *             int field_f;   // 5
		 *//*
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
				result[i] = e;
			}
		}

		return result;
	}*/
    /* 
	private static Field[] readAllFields(Class<?> targetClass) {
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

	private static FieldOption readImplicitFieldOption(Class<?> targetClass) {
		MessagePackMessage a = targetClass.getAnnotation(MessagePackMessage.class);
		if(a == null) {
			return FieldOption.DEFAULT;
		}
		return a.value();
	}

	private static FieldOption readFieldOption(Field field, FieldOption implicitOption) {
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

	private static int readFieldIndex(Field field, int maxIndex) {
		Index a = field.getAnnotation(Index.class);
		if(a == null) {
			return maxIndex + 1;
		} else {
			return a.value();
		}
	}

	private static boolean isAnnotated(AccessibleObject ao, Class<? extends Annotation> with) {
		return ao.getAnnotation(with) != null;
	}*/
}

