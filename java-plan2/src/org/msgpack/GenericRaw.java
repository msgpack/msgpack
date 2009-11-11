package org.msgpack;

import java.nio.charset.Charset;

public class GenericRaw extends GenericObject {
	byte[] bytes;
	String string;

	public GenericRaw()
	{
		this.bytes = new byte[0];
		this.string = null;
	}

	public GenericRaw(byte[] bytes)
	{
		this.bytes = bytes;
		this.string = null;
	}

	public GenericRaw(String string)
	{
		this.bytes = null;
		this.string = string;
	}

	public synchronized void setString(String string)
	{
		this.string = string;
		this.bytes = null;
	}

	public synchronized void setBytes(byte[] bytes)
	{
		this.bytes = bytes;
		this.string = null;
	}

	private static Charset UTF8_CHARSET = Charset.forName("UTF-8");

	@Override
	public synchronized String asString()
	{
		if(string == null) {
			return string = new String(bytes, UTF8_CHARSET);
		}
		return string;
	}

	@Override
	public synchronized byte[] asBytes()
	{
		if(bytes == null) {
			return bytes = string.getBytes(UTF8_CHARSET);
		}
		return bytes;
	}
}

