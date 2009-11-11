package org.msgpack.schema;

import java.util.Map;
import java.util.Arrays;
import java.lang.reflect.Field;
import org.msgpack.*;

public class SpecificFieldSchema extends FieldSchema {
	public Field fieldCache;
	private int index;

	public SpecificFieldSchema(String name, Schema type)
	{
		super(name, type);
		this.index = -1;
	}

	@Override
	public Object getFieldValue(Object obj)
	{
		if(index >= 0) {
			return ((MessageMergeable)obj).getField(index);
		}

		try {
			return fieldCache.get(obj);
		} catch(IllegalArgumentException e) {
			throw new RuntimeException("can't get value from '"+getName()+"' field of '"+obj.getClass().getName()+"' class: "+e.getMessage());
		} catch(IllegalAccessException e) {
			throw new RuntimeException("can't get value from '"+getName()+"' field of '"+obj.getClass().getName()+"' class: "+e.getMessage());
		}
	}

	@Override
	public void setFieldValue(Object obj, Object value)
	{
		if(index >= 0) {
			((MessageMergeable)obj).setField(index, value);
			return;
		}

		try {
			fieldCache.set(obj, value);
		} catch(IllegalArgumentException e) {
			throw new RuntimeException("can't set value into '"+getName()+"' field of '"+obj.getClass().getName()+"' class: "+e.getMessage());
		} catch(IllegalAccessException e) {
			throw new RuntimeException("can't set value into '"+getName()+"' field of '"+obj.getClass().getName()+"' class: "+e.getMessage());
		}
	}

	void cacheField(Class c, int index)
	{
		for(Class i : c.getInterfaces()) {
			if(i.equals(MessageMergeable.class)) {
				this.index = index;
				return;
			}
		}

		try {
			fieldCache = c.getDeclaredField(getName());
			if(!fieldCache.isAccessible()) {
				fieldCache.setAccessible(true);
			}
		} catch(NoSuchFieldException e) {
			throw new RuntimeException("can't get '"+getName()+"' field of '"+c.getName()+"' class: "+e.getMessage());
		} catch(SecurityException e) {
			throw new RuntimeException("can't get '"+getName()+"' field of '"+c.getName()+"' class: "+e.getMessage());
		}
	}

	//public void setFieldInt(Object obj, int value)
	//{
	//	if(type instanceof PrimitiveSchema) {
	//	}
	//}
}

