//
// MessagePack for Java
//
// Copyright (C) 2009-2010 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
package org.msgpack;

import java.lang.Iterable;
import java.io.InputStream;
import java.io.IOException;
import java.util.Iterator;
import org.msgpack.impl.UnpackerImpl;

public class Unpacker extends UnpackerImpl implements Iterable<Object> {

	public static final int DEFAULT_BUFFER_SIZE = 32*1024;

	private int used;
	private int offset;
	private int parsed;
	private byte[] buffer;
	private int bufferReserveSize;
	private InputStream stream;

	public Unpacker() {
		this(DEFAULT_BUFFER_SIZE);
	}

	public Unpacker(int bufferReserveSize) {
		this(null, bufferReserveSize);
	}

	public Unpacker(InputStream stream) {
		this(stream, DEFAULT_BUFFER_SIZE);
	}

	public Unpacker(InputStream stream, int bufferReserveSize) {
		super();
		this.used = 0;
		this.offset = 0;
		this.parsed = 0;
		this.buffer = new byte[bufferReserveSize];
		this.bufferReserveSize = bufferReserveSize/2;
		this.stream = stream;
	}

	public Unpacker useSchema(Schema s) {
		super.setSchema(s);
		return this;
	}

	public void reserveBuffer(int size) {
		if(buffer.length - used >= size) {
			return;
		}
		/*
		if(used == parsed && buffer.length >= size) {
			// rewind buffer
			used = 0;
			offset = 0;
			return;
		}
		*/

		int nextSize = buffer.length * 2;
		while(nextSize < size + used) {
			nextSize *= 2;
		}

		byte[] tmp = new byte[nextSize];
		System.arraycopy(buffer, offset, tmp, 0, used - offset);

		buffer = tmp;
		used -= offset;
		offset = 0;
	}

	public byte[] getBuffer() {
		return buffer;
	}

	public int getBufferOffset() {
		return used;
	}

	public int getBufferCapacity() {
		return buffer.length - used;
	}

	public void bufferConsumed(int size) {
		used += size;
	}

	public void feed(byte[] buffer) {
		feed(buffer, 0, buffer.length);
	}

	public void feed(byte[] buffer, int offset, int length) {
		reserveBuffer(length);
		System.arraycopy(buffer, offset, this.buffer, this.offset, length);
		bufferConsumed(length);
	}

	public boolean fill() throws IOException {
		if(stream == null) {
			return false;
		}
		reserveBuffer(bufferReserveSize);
		int rl = stream.read(getBuffer(), getBufferOffset(), getBufferCapacity());
		if(rl <= 0) {
			return false;
		}
		bufferConsumed(rl);
		return true;
	}

	public Iterator<Object> iterator() {
		return new UnpackIterator(this);
	}

	public boolean execute() throws UnpackException {
		int noffset = super.execute(buffer, offset, used);
		if(noffset <= offset) {
			return false;
		}
		parsed += noffset - offset;
		offset = noffset;
		return super.isFinished();
	}

	public Object getData() {
		return super.getData();
	}

	public void reset() {
		super.reset();
		parsed = 0;
	}

	public int getMessageSize() {
		return parsed - offset + used;
	}

	public int getParsedSize() {
		return parsed;
	}

	public int getNonParsedSize() {
		return used - offset;
	}

	public void skipNonparsedBuffer(int size) {
		offset += size;
	}

	public void removeNonparsedBuffer() {
		used = offset;
	}

	/*
	public static class Context {
		private boolean finished;
		private Object data;
		private int offset;
		private UnpackerImpl impl;

		public Context()
		{
			this.finished = false;
			this.impl = new UnpackerImpl();
		}

		public boolean isFinished()
		{
			return finished;
		}

		public Object getData()
		{
			return data;
		}

		int getOffset()
		{
			return offset;
		}

		void setFinished(boolean finished)
		{
			this.finished = finished;
		}

		void setData(Object data)
		{
			this.data = data;
		}

		void setOffset(int offset)
		{
			this.offset = offset;
		}

		UnpackerImpl getImpl()
		{
			return impl;
		}
	}

	public static int unpack(Context ctx, byte[] buffer) throws UnpackException
	{
		return unpack(ctx, buffer, 0, buffer.length);
	}

	public static int unpack(Context ctx, byte[] buffer, int offset, int length) throws UnpackException
	{
		UnpackerImpl impl = ctx.getImpl();
		int noffset = impl.execute(buffer, offset + ctx.getOffset(), length);
		ctx.setOffset(noffset - offset);
		if(impl.isFinished()) {
			ctx.setData(impl.getData());
			ctx.setFinished(false);
			impl.reset();
		} else {
			ctx.setData(null);
			ctx.setFinished(true);
		}
		int parsed = noffset - offset;
		ctx.setOffset(parsed);
		return noffset;
	}
	*/
}

