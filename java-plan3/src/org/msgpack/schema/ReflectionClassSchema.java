package org.msgpack.schema;

import java.util.Arrays;
import java.util.List;
import java.lang.reflect.*;
import org.msgpack.*;

// FIXME
public abstract class ReflectionClassSchema extends ClassSchema {
	private Constructor constructorCache;

	public ReflectionClassSchema(String name, List<FieldSchema> fields, String namespace, List<String> imports) {
		super(name, namespace, imports, fields);
	}

	/*
	Schema getElementSchema(int index)
	{
		// FIXME check index < fields.length
		fields[index].getSchema();
	}

	Object createFromArray(Object[] obj)
	{
		Object o = newInstance();
		((MessageConvertable)o).messageConvert(obj);
		return o;
	}

	Object newInstance()
	{
		if(constructorCache == null) {
			cacheConstructor();
		}
		try {
			return constructorCache.newInstance((Object[])null);
		} catch (InvocationTargetException e) {
			throw new RuntimeException("can't instantiate "+fqdn+": "+e.getMessage());
		} catch (InstantiationException e) {
			throw new RuntimeException("can't instantiate "+fqdn+": "+e.getMessage());
		} catch (IllegalAccessException e) {
			throw new RuntimeException("can't instantiate "+fqdn+": "+e.getMessage());
		}
	}

	private void cacheConstructor()
	{
		try {
			Class c = Class.forName(fqdn);
			int index = 0;
			for(SpecificFieldSchema f : fields) {
				f.cacheField(c, index++);
			}
			constructorCache = c.getDeclaredConstructor((Class[])null);
			constructorCache.setAccessible(true);
		} catch(ClassNotFoundException e) {
			throw new RuntimeException("class not found: "+fqdn);
		} catch (NoSuchMethodException e) {
			throw new RuntimeException("class not found: "+fqdn+": "+e.getMessage());
		}
	}
	*/
}

