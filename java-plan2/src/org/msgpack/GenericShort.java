package org.msgpack;

public class GenericShort extends GenericObject {
	short value;

	public GenericShort(short value)
	{
		this.value = value;
	}

	@Override
	public short asShort()
	{
		return value;
	}

	@Override
	public int asInt()
	{
		return value;
	}

	@Override
	public long asLong()
	{
		return value;
	}
}

