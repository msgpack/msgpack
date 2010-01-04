package org.msgpack.schema;

import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import org.msgpack.*;


public class GenericClassSchema extends ClassSchema {
	private List<GenericFieldSchema> fields;

	private String fqdn;
	private Constructor constructorCache;

	public GenericClassSchema(String name, List<GenericFieldSchema> fields, String namespace, List<String> imports)
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

	public String getNamespace()
	{
		return namespace;
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
		for(GenericFieldSchema f : fields) {
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
		// FIXME
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object convert(GenericObject obj)
	{
		// FIXME
		return obj;
	}

	@Override
	public Object newInstance()
	{
		return new HashMap(fields.size());
	}
}

