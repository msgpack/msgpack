package org.msgpack.schema;

import java.io.IOException;
import org.msgpack.*;

public class ShortSchema extends Schema {
	public ShortSchema()
	{
		super("Short");
	}

	@Override
	public String getExpression()
	{
		return "short";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		pk.packShort((Short)obj);
	}

	@Override
	public Object convert(GenericObject obj)
	{
		return obj.asShort();
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
}

