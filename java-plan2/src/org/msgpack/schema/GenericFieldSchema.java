package org.msgpack.schema;

import java.util.Map;
import java.lang.reflect.Field;

public final class GenericFieldSchema extends FieldSchema {
	public GenericFieldSchema(String name, Schema type)
	{
		super(name, type);
	}

	@Override
	public Object getFieldValue(Object obj)
	{
		return ((Map)obj).get(getName());
	}

	@Override
	@SuppressWarnings("unchecked")
	public void setFieldValue(Object obj, Object value)
	{
		((Map)obj).put(getName(), value);
	}
}

