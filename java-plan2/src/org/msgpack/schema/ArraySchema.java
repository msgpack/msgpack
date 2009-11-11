package org.msgpack.schema;

import java.util.List;
import java.util.ArrayList;
import java.io.IOException;
import org.msgpack.*;

public class ArraySchema extends Schema {
	private Schema elementType;

	public ArraySchema(Schema elementType)
	{
		super("array");
		this.elementType = elementType;
	}

	public Schema getElementType()
	{
		return elementType;
	}

	@Override
	public String getFullName()
	{
		return "ArrayList<"+elementType.getFullName()+">";
	}

	@Override
	public String getExpression()
	{
		return "(array "+elementType.getExpression()+")";
	}

	@Override
	@SuppressWarnings("unchecked")
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		List<Object> d = (List<Object>)obj;
		pk.packArray(d.size());
		for(Object e : d) {
			elementType.pack(pk, e);
		}
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object convert(GenericObject obj)
	{
		List<GenericObject> d = obj.asArray();
		List<Object> g = new ArrayList<Object>();
		for(GenericObject o : d) {
			g.add( elementType.convert(o) );
		}
		return g;
	}
}

