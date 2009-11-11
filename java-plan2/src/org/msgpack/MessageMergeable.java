package org.msgpack;

public interface MessageMergeable {
	public void setField(int index, Object value);
	public Object getField(int index);
}

