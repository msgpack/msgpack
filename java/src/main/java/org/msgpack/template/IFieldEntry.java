package org.msgpack.template;

import java.lang.reflect.Type;

public interface IFieldEntry {

	public abstract String getName();

	public abstract Class<?> getType();

	public abstract String getJavaTypeName();

	public abstract Type getGenericType();

	public abstract FieldOption getOption();

	public abstract boolean isAvailable();

	public abstract boolean isRequired();

	public abstract boolean isOptional();

	public abstract boolean isNullable();

}