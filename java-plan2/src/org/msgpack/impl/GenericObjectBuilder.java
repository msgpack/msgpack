package org.msgpack.impl;

import org.msgpack.*;

public class GenericObjectBuilder implements ObjectBuilder {
	public Object createNil()
	{
		return null;
	}

	@Override
	public Object createBoolean(boolean v)
	{
		return new GenericBoolean(v);
	}

	@Override
	public Object createByte(byte v)
	{
		//return new GenericByte(v);
		return null;  // FIXME
	}

	@Override
	public Object createShort(short v)
	{
		return new GenericShort(v);
	}

	@Override
	public Object createInt(int v)
	{
		//return new GenericInt(v);
		return null;  // FIXME
	}

	@Override
	public Object createLong(long v)
	{
		return new GenericLong(v);
	}

	@Override
	public Object createFloat(float v)
	{
		//return new GenericFloat(v);
		return null;  // FIXME
	}

	@Override
	public Object createDouble(double v)
	{
		//return new GenericDouble(v);
		return null;  // FIXME
	}

	@Override
	public Object createRaw(byte[] b, int offset, int length)
	{
		byte[] copy = new byte[length];
		System.arraycopy(b, offset, copy, 0, length);
		return new GenericRaw(copy);
	}

	@Override
	public ArrayBuilder createArray(int length)
	{
		return new GenericArrayBuilder(length);
	}

	@Override
	public MapBuilder createMap(int length)
	{
		return new GenericMapBuilder(length);
	}
}

final class GenericArrayBuilder implements ArrayBuilder {
	private GenericArray a;

	GenericArrayBuilder(int length)
	{
		this.a = new GenericArray(length);
	}

	@Override
	public void add(Object element)
	{
		a.add((GenericObject)element);
	}

	@Override
	public Object finish()
	{
		return a;
	}
}

final class GenericMapBuilder implements MapBuilder {
	private GenericMap m;
	private GenericObject key;

	GenericMapBuilder(int length)
	{
		this.m = new GenericMap(length);
	}

	@Override
	public void putKey(Object key)
	{
		this.key = (GenericObject)key;
	}

	@Override
	public void putValue(Object value)
	{
		m.put(this.key, (GenericObject)value);
		this.key = null;
	}

	@Override
	public Object finish()
	{
		return m;
	}
}

