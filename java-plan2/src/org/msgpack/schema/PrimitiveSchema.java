package org.msgpack.schema;

public abstract class PrimitiveSchema extends Schema {
	public static enum PrimitiveType {
		BYTE,
		SHORT,
		INT,
		LONG,
		FLOAT,
		DOUBLE,
	}

	public final PrimitiveType type;

	protected PrimitiveSchema(String name, PrimitiveType type)
	{
		super(name);
		this.type = type;
	}
}

