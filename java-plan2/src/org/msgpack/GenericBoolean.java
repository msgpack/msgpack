package org.msgpack;

public class GenericBoolean extends GenericObject {
	boolean value;

	public GenericBoolean(boolean value)
	{
		this.value = value;
	}

	@Override
	public boolean asBoolean()
	{
		return value;
	}
}

