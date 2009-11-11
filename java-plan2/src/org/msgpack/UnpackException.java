package org.msgpack;

public class UnpackException extends MessagePackException
{
	public static final int EXTRA_BYTES         =  1;
	public static final int INSUFFICIENT_BYTES  =  0;
	public static final int PARSE_ERROR         = -1;

	private int errorCode;
	private Object data;

	public UnpackException(String message, int errorCode)
	{
		super(message);
		this.errorCode = errorCode;
	}

	public UnpackException(String message, int errorCode, Object data)
	{
		super(message);
		this.errorCode = errorCode;
		this.data = data;
	}

	public int getErrorCode()
	{
		return errorCode;
	}

	public Object getData()
	{
		return data;
	}
}

