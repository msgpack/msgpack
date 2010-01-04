package org.msgpack.schema;

import java.io.IOException;
import org.msgpack.*;

public class IntSchema extends Schema {
	public IntSchema()
	{
		super("Integer");
	}

	@Override
	public String getExpression()
	{
		return "int";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		pk.packInt((Integer)obj);
	}

	@Override
	public Object convert(GenericObject obj)
	{
		return obj.asInt();
	}

	@Override
	public Object createByte(byte v)
	{
		return (int)v;
	}

	@Override
	public Object createShort(short v)
	{
		return (int)v;
	}

	@Override
	public Object createInt(int v)
	{
		return (int)v;
	}

	@Override
	public Object createLong(long v)
	{
		return (int)v;
	}
}

