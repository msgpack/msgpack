package org.msgpack.impl;

public interface ObjectBuilder {
	public Object createNil();
	public Object createBoolean(boolean v);
	public Object createByte(byte v);
	public Object createShort(short v);
	public Object createInt(int v);
	public Object createLong(long v);
	public Object createFloat(float v);
	public Object createDouble(double v);
	public Object createRaw(byte[] b, int offset, int length);
	public ArrayBuilder createArray(int length);
	public MapBuilder createMap(int length);
}

