package org.msgpack;

import java.util.Map;
import java.util.HashMap;

public class GenericMap extends GenericObject {
	private HashMap<GenericObject,GenericObject> map;

	public GenericMap(int length)
	{
		this.map = new HashMap<GenericObject,GenericObject>(length);
	}

	public void put(GenericObject key, GenericObject value)
	{
		map.put(key, value);
	}

	@Override
	public Map<GenericObject,GenericObject> asMap()
	{
		return map;
	}
}

