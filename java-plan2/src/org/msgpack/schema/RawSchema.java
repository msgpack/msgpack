package org.msgpack.schema;

import java.io.IOException;
import java.nio.charset.Charset;
import org.msgpack.*;

public class RawSchema extends Schema {
	public RawSchema()
	{
		super("raw");
	}

	public String getFullName()
	{
		return "byte[]";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		byte[] d = (byte[])obj;
		pk.packRaw(d.length);
		pk.packRawBody(d);
	}

	@Override
	public Object convert(GenericObject obj)
	{
		return obj.asBytes();
	}

	@Override
	public Object createRaw(byte[] b, int offset, int length)
	{
		byte[] d = new byte[length];
		System.arraycopy(b, offset, d, 0, length);
		return d;
	}
}

