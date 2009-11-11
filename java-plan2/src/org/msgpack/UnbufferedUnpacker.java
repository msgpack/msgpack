package org.msgpack;

import java.lang.Iterable;
import java.io.InputStream;
import java.io.IOException;
import java.util.Iterator;
import org.msgpack.impl.*;
import org.msgpack.schema.Schema;

public class UnbufferedUnpacker extends UnpackerImpl {
	private int offset;
	private boolean finished;
	private Object data;

	public UnbufferedUnpacker()
	{
		super(new GenericObjectBuilder());
		this.offset = 0;
		this.finished = false;
	}

	public UnbufferedUnpacker useSchema(Schema s)
	{
		super.setBuilder(new SpecificObjectBuilder(s));
		return this;
	}

	public Object getData()
	{
		return data;
	}

	public boolean isFinished()
	{
		return finished;
	}

	public void reset()
	{
		super.reset();
		this.offset = 0;
	}

	int getOffset()
	{
		return offset;
	}

	void setOffset(int offset)
	{
		this.offset = offset;
	}

	public int execute(byte[] buffer) throws UnpackException
	{
		return execute(buffer, 0, buffer.length);
	}

	// FIXME
	public int execute(byte[] buffer, int offset, int length) throws UnpackException
	{
		int noffset = super.execute(buffer, offset + this.offset, length);
		this.offset = noffset - offset;
		if(super.isFinished()) {
			this.data = super.getData();
			this.finished = true;
			super.reset();
		} else {
			this.finished = false;
		}
		return noffset;
	}
}

