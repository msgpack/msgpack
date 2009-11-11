package org.msgpack.schema;

public abstract class FieldSchema {
	private String name;
	private Schema type;

	public FieldSchema(String name, Schema type)
	{
		this.name = name;
		this.type = type;
	}

	public String getName()
	{
		return this.name;
	}

	public Schema getType()
	{
		return type;
	}

	public String getExpression()
	{
		return "(field "+name+" "+type.getExpression()+")";
	}

	public abstract Object getFieldValue(Object obj);
	public abstract void setFieldValue(Object obj, Object value);
}

