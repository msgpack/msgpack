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
import java.nio.ByteBuffer;

public class Unpacker implements Iterable<Object> {

	// buffer:
	// +---------------------------------------------+
	// | [object] | [obje| unparsed ... | unused  ...|
	// +---------------------------------------------+
	//            ^ parsed
	//                   ^ offset
	//                                  ^ filled
	//                                               ^ buffer.length

	private static final int DEFAULT_BUFFER_SIZE = 32*1024;

	protected int parsed;
	protected int bufferReserveSize;
	protected InputStream stream;

	class BufferedUnpackerMixin extends BufferedUnpackerImpl {
		boolean fill() throws IOException {
			if(stream == null) {
				return false;
			}
			reserveBuffer(bufferReserveSize);
			int rl = stream.read(buffer, filled, buffer.length - filled);
			// equals: stream.read(getBuffer(), getBufferOffset(), getBufferCapacity());
			if(rl <= 0) {
				return false;
			}
			bufferConsumed(rl);
			return true;
		}
	};

	final BufferedUnpackerMixin impl = new BufferedUnpackerMixin();


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
		this.parsed = 0;
		this.bufferReserveSize = bufferReserveSize/2;
		this.stream = stream;
	}

	public Unpacker useSchema(Schema s) {
		impl.setSchema(s);
		return this;
	}


	public InputStream getStream() {
		return this.stream;
	}

	public void setStream(InputStream stream) {
		this.stream = stream;
	}

	public void feed(ByteBuffer buffer) {
		int length = buffer.remaining();
		if (length == 0) return;
		reserveBuffer(length);
		buffer.get(impl.buffer, impl.offset, length);
		bufferConsumed(length);
	}

	public void feed(byte[] buffer) {
		feed(buffer, 0, buffer.length);
	}

	public void feed(byte[] buffer, int offset, int length) {
		reserveBuffer(length);
		System.arraycopy(buffer, offset, impl.buffer, impl.offset, length);
		bufferConsumed(length);
	}

	public boolean fill() throws IOException {
		return impl.fill();
	}

	public Iterator<Object> iterator() {
		return new UnpackIterator(this);
	}

	public UnpackResult next() throws IOException, UnpackException {
		UnpackResult result = new UnpackResult();
		impl.next(result);
		return result;
	}

	public boolean next(UnpackResult result) throws IOException, UnpackException {
		return impl.next(result);
	}


	public void reserveBuffer(int require) {
		if(impl.buffer == null) {
			int nextSize = (bufferReserveSize < require) ? require : bufferReserveSize;
			impl.buffer = new byte[nextSize];
			return;
		}

		if(impl.buffer.length - impl.filled >= require) {
			return;
		}

		int nextSize = impl.buffer.length * 2;
		int notParsed = impl.filled - impl.offset;
		while(nextSize < require + notParsed) {
			nextSize *= 2;
		}

		byte[] tmp = new byte[nextSize];
		System.arraycopy(impl.buffer, impl.offset, tmp, 0, impl.filled - impl.offset);

		impl.buffer = tmp;
		impl.filled = notParsed;
		impl.offset = 0;
	}

	public byte[] getBuffer() {
		return impl.buffer;
	}

	public int getBufferOffset() {
		return impl.filled;
	}

	public int getBufferCapacity() {
		return impl.buffer.length - impl.filled;
	}

	public void bufferConsumed(int size) {
		impl.filled += size;
	}

	public boolean execute() throws UnpackException {
		int noffset = impl.execute(impl.buffer, impl.offset, impl.filled);
		if(noffset <= impl.offset) {
			return false;
		}
		parsed += noffset - impl.offset;
		impl.offset = noffset;
		return impl.isFinished();
	}


	public int execute(byte[] buffer) throws UnpackException {
		return execute(buffer, 0, buffer.length);
	}

	public int execute(byte[] buffer, int offset, int length) throws UnpackException {
		int noffset = impl.execute(buffer, offset + impl.offset, length);
		impl.offset = noffset - offset;
		if(impl.isFinished()) {
			impl.resetState();
		}
		return noffset;
	}

	public boolean isFinished() {
		return impl.isFinished();
	}

	public Object getData() {
		return impl.getData();
	}

	public void reset() {
		impl.reset();
	}

	public int getMessageSize() {
		return parsed - impl.offset + impl.filled;
	}

	public int getParsedSize() {
		return parsed;
	}

	public int getNonParsedSize() {
		return impl.filled - impl.offset;
	}

	public void skipNonparsedBuffer(int size) {
		impl.offset += size;
	}

	public void removeNonparsedBuffer() {
		impl.filled = impl.offset;
	}


	final public byte unpackByte() throws IOException, MessageTypeException {
		return impl.unpackByte();
	}

	final public short unpackShort() throws IOException, MessageTypeException {
		return impl.unpackShort();
	}

	final public int unpackInt() throws IOException, MessageTypeException {
		return impl.unpackInt();
	}

	final public long unpackLong() throws IOException, MessageTypeException {
		return impl.unpackLong();
	}

	final public float unpackFloat() throws IOException, MessageTypeException {
		return impl.unpackFloat();
	}

	final public double unpackDouble() throws IOException, MessageTypeException {
		return impl.unpackDouble();
	}

	final public Object unpackNull() throws IOException, MessageTypeException {
		return impl.unpackNull();
	}

	final public boolean unpackBoolean() throws IOException, MessageTypeException {
		return impl.unpackBoolean();
	}

	final public int unpackArray() throws IOException, MessageTypeException {
		return impl.unpackArray();
	}

	final public int unpackMap() throws IOException, MessageTypeException {
		return impl.unpackMap();
	}

	final public int unpackRaw() throws IOException, MessageTypeException {
		return impl.unpackRaw();
	}

	final public byte[] unpackRawBody(int length) throws IOException, MessageTypeException {
		return impl.unpackRawBody(length);
	}

	final public String unpackString() throws IOException, MessageTypeException {
		return impl.unpackString();
	}

	final public Object unpackObject() throws IOException, MessageTypeException {
		return impl.unpackObject();
	}
}

