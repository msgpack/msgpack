package org.msgpack.schema;

import java.util.List;
import java.util.Map;
import java.io.IOException;
import java.util.Iterator;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import org.msgpack.*;

public class SpecificClassSchema extends ClassSchema {
	private List<SpecificFieldSchema> fields;
	private String namespace;
	private List<String> imports;

	private String fqdn;
	private Constructor constructorCache;

	public SpecificClassSchema(String name, List<SpecificFieldSchema> fields, String namespace, List<String> imports)
	{
		super(name, namespace, imports);
		this.fields = fields;
		if(namespace == null) {
			this.fqdn = name;
		} else {
			this.fqdn = namespace+"."+name;
		}
	}

	//@Override
	//public String getFullName()
	//{
	//	if(namespace == null) {
	//		return getName();
	//	} else {
	//		return namespace+"."+getName();
	//	}
	//}

	public List<? extends FieldSchema> getFields()
	{
		return fields;
	}

	@Override
	public String getExpression()
	{
		StringBuffer b = new StringBuffer();
		b.append("(class ");
		b.append(getName());
		if(namespace != null) {
			b.append(" (package "+namespace+")");
		}
		for(SpecificFieldSchema f : fields) {
			b.append(" "+f.getExpression());
		}
		b.append(")");
		return b.toString();
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}

		if(constructorCache == null) {
			cacheConstructor();
		}

		pk.packArray(fields.size());
		for(SpecificFieldSchema f : fields) {
			f.getType().pack(pk, f.getFieldValue(obj));
		}
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object convert(GenericObject obj)
	{
		if(constructorCache == null) {
			cacheConstructor();
		}

		List<GenericObject> d = obj.asArray();

		try {
			Object g = constructorCache.newInstance((Object[])null);

			Iterator<GenericObject> vi = d.iterator();
			Iterator<SpecificFieldSchema> fi = fields.iterator();
			while(fi.hasNext() && vi.hasNext()) {
				SpecificFieldSchema f = fi.next();
				GenericObject v = vi.next();
				f.setFieldValue(g, f.getType().convert(v));
			}
			// leave it as uninitialized
			//while(fi.hasNext()) {
			//	SpecificFieldSchema f = fi.next();
			//	g.put(f.getName(), null);
			//}

			return g;

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

	@Override
	public Object newInstance()
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

	public boolean equals(SpecificClassSchema o)
	{
		return (namespace != null ? namespace.equals(o.getNamespace()) : o.getNamespace() == null) &&
			getName().equals(o.getName());
	}
}

