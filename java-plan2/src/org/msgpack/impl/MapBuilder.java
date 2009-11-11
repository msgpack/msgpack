package org.msgpack.impl;

public interface MapBuilder {
	public void putKey(Object key);
	public void putValue(Object value);
	public Object finish();
}

