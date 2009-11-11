package org.msgpack;

import java.util.List;
import java.util.Map;

public abstract class GenericObject {
	public boolean asBoolean()
	{
		throw new RuntimeException("type error");
	}

	public byte asByte()
	{
		throw new RuntimeException("type error");
	}

	public short asShort()
	{
		throw new RuntimeException("type error");
	}

	public int asInt()
	{
		throw new RuntimeException("type error");
	}

	public long asLong()
	{
		throw new RuntimeException("type error");
	}

	public String asString()
	{
		throw new RuntimeException("type error");
	}

	public byte[] asBytes()
	{
		throw new RuntimeException("type error");
	}

	public List<GenericObject> asArray()
	{
		throw new RuntimeException("type error");
	}

	public Map<GenericObject,GenericObject> asMap()
	{
		throw new RuntimeException("type error");
	}
}

