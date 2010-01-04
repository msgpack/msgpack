package org.msgpack.schema;

import java.io.IOException;
import org.msgpack.*;

public class ObjectSchema extends Schema {
	public ObjectSchema()
	{
		super("object");
	}

	public String getFullName()
	{
		return "GenericObject";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		pk.pack(obj);
	}

	@Override
	public Object convert(GenericObject obj)
	{
		return obj;
	}
}

