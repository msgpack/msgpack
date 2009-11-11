package org.msgpack;

public class GenericLong extends GenericObject {
	long value;

	public GenericLong(long value)
	{
		this.value = value;
	}

	@Override
	public long asLong()
	{
		return value;
	}
}

