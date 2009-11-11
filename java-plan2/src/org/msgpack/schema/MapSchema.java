package org.msgpack.schema;

import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.io.IOException;
import org.msgpack.*;

public class MapSchema extends Schema {
	private Schema keyType;
	private Schema valueType;

	public MapSchema(Schema keyType, Schema valueType)
	{
		super("map");
		this.keyType = keyType;
		this.valueType = valueType;
	}

	public Schema getKeyType()
	{
		return keyType;
	}

	public Schema getValueType()
	{
		return valueType;
	}

	@Override
	public String getFullName()
	{
		return "HashList<"+keyType.getFullName()+", "+valueType.getFullName()+">";
	}

	@Override
	public String getExpression()
	{
		return "(map "+keyType.getExpression()+" "+valueType.getExpression()+")";
	}

	@Override
	@SuppressWarnings("unchecked")
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj == null) {
			pk.packNil();
			return;
		}
		Map<Object,Object> d = (Map<Object,Object>)obj;
		pk.packMap(d.size());
		for(Map.Entry<Object,Object> e : d.entrySet()) {
			keyType.pack(pk, e.getKey());
			valueType.pack(pk, e.getValue());
		}
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object convert(GenericObject obj)
	{
		Map<GenericObject,GenericObject> d = obj.asMap();
		Map<Object,Object> g = new HashMap<Object,Object>();
		for(Map.Entry<GenericObject,GenericObject> e : d.entrySet()) {
			g.put(keyType.convert(e.getKey()), valueType.convert(e.getValue()));
		}
		return g;
	}
}

