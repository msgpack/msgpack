package org.msgpack.schema;

import java.io.IOException;
import org.msgpack.impl.*;
import org.msgpack.Packer;
import org.msgpack.GenericObject;

public abstract class Schema {
	private String expression;
	private String name;

	public Schema(String name)
	{
		this.expression = expression;
		this.name = name;
	}

	public String getName()
	{
		return name;
	}

	public String getFullName()
	{
		return name;
	}

	public String getExpression()
	{
		return name;
	}

	public static Schema parse(String source)
	{
		return SSchemaParser.parse(source);
	}

	public static Schema load(String source)
	{
		return SSchemaParser.load(source);
	}

	public abstract void pack(Packer pk, Object obj) throws IOException;
	public abstract Object convert(GenericObject obj);
	//public abstract Object convertGeneric(GenericObject obj);


	public Object createNil()
	{
		return null;
	}

	public Object createBoolean(boolean v)
	{
		throw new RuntimeException("type error");
	}

	public Object createByte(byte v)
	{
		throw new RuntimeException("type error");
	}

	public Object createShort(short v)
	{
		throw new RuntimeException("type error");
	}

	public Object createInt(int v)
	{
		throw new RuntimeException("type error");
	}

	public Object createLong(long v)
	{
		throw new RuntimeException("type error");
	}

	public Object createFloat(float v)
	{
		throw new RuntimeException("type error");
	}

	public Object createDouble(double v)
	{
		throw new RuntimeException("type error");
	}

	public Object createRaw(byte[] b, int offset, int length)
	{
		throw new RuntimeException("type error");
	}
}

