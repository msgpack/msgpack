package org.msgpack.schema;

import java.io.IOException;
import org.msgpack.*;

public class LongSchema extends Schema {
	public LongSchema()
	{
		super("Long");
	}

	@Override
	public String getExpression()
	{
		return "long";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		pk.packLong((Long)obj);
	}

	@Override
	public Object convert(GenericObject obj)
	{
		return obj.asLong();
	}

	@Override
	public Object createByte(byte v)
	{
		return (long)v;
	}

	@Override
	public Object createShort(short v)
	{
		return (long)v;
	}

	@Override
	public Object createInt(int v)
	{
		return (long)v;
	}

	@Override
	public Object createLong(long v)
	{
		return (long)v;
	}
}

