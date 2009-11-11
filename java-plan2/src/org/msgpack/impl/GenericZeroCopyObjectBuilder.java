package org.msgpack.impl;

import org.msgpack.*;

public class GenericZeroCopyObjectBuilder extends GenericObjectBuilder {
	@Override
	public Object createRaw(byte[] b, int offset, int length)
	{
		return new GenericRawRef(b, offset, length);
	}
}

