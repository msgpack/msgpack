package org.msgpack.schema;

import java.io.IOException;
import java.nio.charset.Charset;
import org.msgpack.*;

public class StringSchema extends Schema {
	public StringSchema()
	{
		super("string");
	}

	public String getFullName()
	{
		return "String";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		String s = (String)obj;
		byte[] d = s.getBytes("UTF-8");
		pk.packRaw(d.length);
		pk.packRawBody(d);
	}

	@Override
	public Object convert(GenericObject obj)
	{
		return obj.asString();
	}

	@Override
	public Object createRaw(byte[] b, int offset, int length)
	{
		try {
			return new String(b, offset, length, "UTF-8");  // XXX FIXME debug
		} catch (Exception e) {
			// FIXME
			throw new RuntimeException(e.getMessage());
		}
	}
}

