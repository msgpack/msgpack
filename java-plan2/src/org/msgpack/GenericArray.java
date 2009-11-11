package org.msgpack;

import java.util.List;
import java.util.ArrayList;

public class GenericArray extends GenericObject {
	private ArrayList<GenericObject> array;

	public GenericArray(int length)
	{
		this.array = new ArrayList<GenericObject>(length);
	}

	public void add(GenericObject element)
	{
		array.add(element);
	}

	@Override
	public List<GenericObject> asArray()
	{
		return array;
	}
}

