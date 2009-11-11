package org.msgpack.impl;

public interface ArrayBuilder {
	public void add(Object element);
	public Object finish();
}

