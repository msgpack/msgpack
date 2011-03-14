package org.msgpack.template;

import java.lang.annotation.Annotation;
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

import org.msgpack.annotation.Ignore;
import org.msgpack.annotation.Index;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.Nullable;
import org.msgpack.annotation.Optional;
import org.msgpack.annotation.Required;
import org.msgpack.template.builder.TemplateBuildException;

public class FieldEntryReader implements IFieldEntryReader{


	public IFieldEntry[] convertFieldEntries(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
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
	
	@Override
	public IFieldEntry[] readFieldEntries(Class<?> targetClass,
			FieldOption implicitOption) {
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
				result[i] = e;
			}
		}

		return result;
	}

	public FieldOption readImplicitFieldOption(Class<?> targetClass) {
		MessagePackMessage a = targetClass.getAnnotation(MessagePackMessage.class);
		if(a == null) {
			return FieldOption.DEFAULT;
		}
		return a.value();
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
	}
	
}
