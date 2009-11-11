package org.msgpack;

import java.io.IOException;

public interface MessagePackable
{
	public void messagePack(Packer pk) throws IOException;
}

