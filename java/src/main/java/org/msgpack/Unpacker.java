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
import java.math.BigInteger;
import org.msgpack.template.TemplateRegistry;

/**
 * Unpacker enables you to deserialize objects from stream.
 *
 * Unpacker provides Buffered API, Unbuffered API and
 * Direct Conversion API.
 *
 * Buffered API uses the internal buffer of the Unpacker.
 * Following code uses Buffered API with an InputStream:
 * <pre>
 * // create an unpacker with input stream
 * Unpacker pac = new Unpacker(System.in);
 *
 * // take a object out using next() method, or ...
 * UnpackResult result = pac.next();
 *
 * // use an iterator.
 * for(MessagePackObject obj : pac) {
 *   // use MessageConvertable interface to convert the
 *   // the generic object to the specific type.
 * }
 * </pre>
 *
 * Following code doesn't use the input stream and feeds buffer
 * using {@link feed(byte[])} method. This is useful to use
 * special stream like zlib or event-driven I/O library.
 * <pre>
 * // create an unpacker without input stream
 * Unpacker pac = new Unpacker();
 *
 * // feed buffer to the internal buffer.
 * pac.feed(input_bytes);
 *
 * // use next() method or iterators.
 * for(MessagePackObject obj : pac) {
 *   // ...
 * }
 * </pre>
 *
 * The combination of {@link reserveBuffer()}, {@link getBuffer()},
 * {@link getBufferOffset()}, {@link getBufferCapacity()} and
 * {@link bufferConsumed()} is useful to omit copying.
 * <pre>
 * // create an unpacker without input stream
 * Unpacker pac = new Unpacker();
 *
 * // reserve internal buffer at least 1024 bytes.
 * pac.reserveBuffer(1024);
 *
 * // feed buffer to the internal buffer upto pac.getBufferCapacity() bytes.
 * System.in.read(pac.getBuffer(), pac.getBufferOffset(), pac.getBufferCapacity());
 *
 * // use next() method or iterators.
 * for(MessagePackObject obj : pac) {
 *     // ...
 * }
 * </pre>
 *
 * Unbuffered API doesn't initialize the internal buffer.
 * You can manage the buffer manually.
 * <pre>
 * // create an unpacker with input stream
 * Unpacker pac = new Unpacker(System.in);
 *
 * // manage the buffer manually.
 * byte[] buffer = new byte[1024];
 * int filled = System.in.read(buffer);
 * int offset = 0;
 *
 * // deserialize objects using execute() method.
 * int nextOffset = pac.execute(buffer, offset, filled);
 *
 * // take out object if deserialized object is ready.
 * if(pac.isFinished()) {
 *     MessagePackObject obj = pac.getData();
 *     // ...
 * }
 * </pre>
 */
public class Unpacker implements Iterable<MessagePackObject> {
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

	final class BufferedUnpackerMixin extends BufferedUnpackerImpl {
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


	/**
	 * Calls {@link Unpacker(DEFAULT_BUFFER_SIZE)}
	 */
	public Unpacker() {
		this(DEFAULT_BUFFER_SIZE);
	}

	/**
	 * Calls {@link Unpacker(null, bufferReserveSize)}
	 */
	public Unpacker(int bufferReserveSize) {
		this(null, bufferReserveSize);
	}

	/**
	 * Calls {@link Unpacker(stream, DEFAULT_BUFFER_SIZE)}
	 */
	public Unpacker(InputStream stream) {
		this(stream, DEFAULT_BUFFER_SIZE);
	}

	/**
	 * Constructs the unpacker.
	 * The stream is used to fill the buffer when more buffer is required by {@link next()} or {@link UnpackIterator#hasNext()} method.
	 * @param stream input stream to fill the buffer
	 * @param bufferReserveSize threshold size to expand the size of buffer
	 */
	public Unpacker(InputStream stream, int bufferReserveSize) {
		this.parsed = 0;
		this.bufferReserveSize = bufferReserveSize/2;
		this.stream = stream;
	}


	/**
	 * Gets the input stream.
	 * @return the input stream. it may be null.
	 */
	public InputStream getStream() {
		return this.stream;
	}

	/**
	 * Sets the input stream.
	 * @param stream the input stream to set.
	 */
	public void setStream(InputStream stream) {
		this.stream = stream;
	}


	/**
	 * Fills the buffer with the specified buffer.
	 */
	public void feed(byte[] buffer) {
		feed(buffer, 0, buffer.length);
	}

	/**
	 * Fills the buffer with the specified buffer.
	 */
	public void feed(byte[] buffer, int offset, int length) {
		reserveBuffer(length);
		System.arraycopy(buffer, offset, impl.buffer, impl.offset, length);
		bufferConsumed(length);
	}

	/**
	 * Fills the buffer with the specified buffer.
	 */
	public void feed(ByteBuffer buffer) {
		int length = buffer.remaining();
		if (length == 0) return;
		reserveBuffer(length);
		buffer.get(impl.buffer, impl.offset, length);
		bufferConsumed(length);
	}

	/**
	 * Swaps the internal buffer with the specified buffer.
	 * This method doesn't copy the buffer and the its contents will be rewritten by {@link fill()} or {@link feed(byte[])} method.
	 */
	public void wrap(byte[] buffer) {
		wrap(buffer, 0, buffer.length);
	}

	/**
	 * Swaps the internal buffer with the specified buffer.
	 * This method doesn't copy the buffer and the its contents will be rewritten by {@link fill()} or {@link feed(byte[])} method.
	 */
	public void wrap(byte[] buffer, int offset, int length) {
		impl.buffer = buffer;
		impl.offset = offset;
		impl.filled = length;
		impl.bufferReferenced = false;  // TODO zero-copy buffer
	}

	/**
	 * Fills the internal using the input stream.
	 * @return false if the stream is null or stream.read returns <= 0.
	 */
	public boolean fill() throws IOException {
		return impl.fill();
	}


	/**
	 * Returns the iterator that calls {@link next()} method repeatedly.
	 */
	public Iterator<MessagePackObject> iterator() {
		return new UnpackIterator(this);
	}

	/**
	 * Deserializes one object and returns it.
	 * @return {@link UnpackResult#isFinished()} returns false if the buffer is insufficient to deserialize one object.
	 */
	public UnpackResult next() throws IOException, UnpackException {
		UnpackResult result = new UnpackResult();
		impl.next(result);
		return result;
	}

	/**
	 * Deserializes one object and returns it.
	 * @return false if the buffer is insufficient to deserialize one object.
	 */
	public boolean next(UnpackResult result) throws IOException, UnpackException {
		return impl.next(result);
	}


	/**
	 * Reserve free space of the internal buffer at least specified size and expands {@link getBufferCapacity()}.
	 */
	public void reserveBuffer(int require) {
		if(impl.buffer == null) {
			int nextSize = (bufferReserveSize < require) ? require : bufferReserveSize;
			impl.buffer = new byte[nextSize];
			impl.bufferReferenced = false;  // TODO zero-copy buffer
			return;
		}

		if(!impl.bufferReferenced) {  // TODO zero-copy buffer
			if(impl.filled <= impl.offset) {
				// rewind the buffer
				impl.filled = 0;
				impl.offset = 0;
			}
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
		impl.bufferReferenced = false;  // TODO zero-copy buffer
	}

	/**
	 * Returns the internal buffer.
	 */
	public byte[] getBuffer() {
		return impl.buffer;
	}

	/**
	 * Returns the size of free space of the internal buffer.
	 */
	public int getBufferCapacity() {
		return impl.buffer.length - impl.filled;
	}

	/**
	 * Returns the offset of free space in the internal buffer.
	 */
	public int getBufferOffset() {
		return impl.filled;
	}

	/**
	 * Moves front the offset of the free space in the internal buffer.
	 * Call this method after fill the buffer manually using {@link reserveBuffer()}, {@link getBuffer()}, {@link getBufferOffset()} and {@link getBufferCapacity()} methods.
	 */
	public void bufferConsumed(int size) {
		impl.filled += size;
	}

	/**
	 * Deserializes one object upto the offset of the internal buffer.
	 * Call {@link reset()} method before calling this method again.
	 * @return true if one object is deserialized. Use {@link getData()} to get the deserialized object.
	 */
	public boolean execute() throws UnpackException {
		int noffset = impl.execute(impl.buffer, impl.offset, impl.filled);
		if(noffset <= impl.offset) {
			return false;
		}
		parsed += noffset - impl.offset;
		impl.offset = noffset;
		return impl.isFinished();
	}


	/**
	 * Deserializes one object over the specified buffer.
	 * This method doesn't use the internal buffer.
	 * Use {@link isFinished()} method to known a object is ready to get.
	 * Call {@link reset()} method before calling this method again.
	 * @return offset position that is parsed.
	 */
	public int execute(byte[] buffer) throws UnpackException {
		return execute(buffer, 0, buffer.length);
	}

	/**
	 * Deserializes one object over the specified buffer.
	 * This method doesn't use the internal buffer.
	 * Use {@link isFinished()} method to known a object is ready to get.
	 * Call {@link reset()} method before calling this method again.
	 * @return offset position that is parsed.
	 */
	public int execute(byte[] buffer, int offset, int length) throws UnpackException {
		int noffset = impl.execute(buffer, offset + impl.offset, length);
		impl.offset = noffset - offset;
		if(impl.isFinished()) {
			impl.resetState();
		}
		return noffset;
	}

	/**
	 * Gets the object deserialized by {@link execute(byte[])} method.
	 */
	public MessagePackObject getData() {
		return impl.getData();
	}

	/**
	 * Returns true if an object is ready to get with {@link getData()} method.
	 */
	public boolean isFinished() {
		return impl.isFinished();
	}

	/**
	 * Resets the internal state of the unpacker.
	 */
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


	/**
	 * Gets one {@code byte} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code byte}.
	 */
	public byte unpackByte() throws IOException, MessageTypeException {
		return impl.unpackByte();
	}

	/**
	 * Gets one {@code short} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code short}.
	 */
	public short unpackShort() throws IOException, MessageTypeException {
		return impl.unpackShort();
	}

	/**
	 * Gets one {@code int} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code int}.
	 */
	public int unpackInt() throws IOException, MessageTypeException {
		return impl.unpackInt();
	}

	/**
	 * Gets one {@code long} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code long}.
	 */
	public long unpackLong() throws IOException, MessageTypeException {
		return impl.unpackLong();
	}

	/**
	 * Gets one {@code BigInteger} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code BigInteger}.
	 */
	public BigInteger unpackBigInteger() throws IOException, MessageTypeException {
		return impl.unpackBigInteger();
	}

	/**
	 * Gets one {@code float} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code float}.
	 */
	public float unpackFloat() throws IOException, MessageTypeException {
		return impl.unpackFloat();
	}

	/**
	 * Gets one {@code double} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code double}.
	 */
	public double unpackDouble() throws IOException, MessageTypeException {
		return impl.unpackDouble();
	}

	/**
	 * Gets one {@code null} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code null}.
	 */
	public Object unpackNull() throws IOException, MessageTypeException {
		return impl.unpackNull();
	}

	/**
	 * Gets one {@code boolean} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code boolean}.
	 */
	public boolean unpackBoolean() throws IOException, MessageTypeException {
		return impl.unpackBoolean();
	}

	/**
	 * Gets one array header from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @return the length of the map. There are {@code retval} objects to get.
	 * @throws MessageTypeException the first value of the buffer is not a array.
	 */
	public int unpackArray() throws IOException, MessageTypeException {
		return impl.unpackArray();
	}

	/**
	 * Gets one map header from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @return the length of the map. There are {@code retval * 2} objects to get.
	 * @throws MessageTypeException the first value of the buffer is not a map.
	 */
	public int unpackMap() throws IOException, MessageTypeException {
		return impl.unpackMap();
	}

	/**
	 * Gets one raw header from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @return the length of the raw bytes. There are {@code retval} bytes to get.
	 * @throws MessageTypeException the first value of the buffer is not a raw bytes.
	 */
	public int unpackRaw() throws IOException, MessageTypeException {
		return impl.unpackRaw();
	}

	/**
	 * Gets one raw body from the buffer.
	 * This method calls {@link fill()} method if needed.
	 */
	public byte[] unpackRawBody(int length) throws IOException {
		return impl.unpackRawBody(length);
	}


	/**
	 * Gets one raw object (header + body) from the buffer.
	 * This method calls {@link fill()} method if needed.
	 */
	public byte[] unpackByteArray() throws IOException {
		return impl.unpackByteArray();
	}

	/**
	 * Gets one raw object (header + body) from the buffer.
	 * This method calls {@link fill()} method if needed.
	 */
	public ByteBuffer unpackByteBuffer() throws IOException {
		return impl.unpackByteBuffer();
	}

	/**
	 * Gets one {@code String} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 * @throws MessageTypeException the first value of the buffer is not a {@code String}.
	 */
	final public String unpackString() throws IOException, MessageTypeException {
		return impl.unpackString();
	}

	/**
	 * Gets one {@code Object} value from the buffer.
	 * This method calls {@link fill()} method if needed.
	 */
	final public MessagePackObject unpackObject() throws IOException {
		return impl.unpackObject();
	}

	final public boolean tryUnpackNull() throws IOException {
		return impl.tryUnpackNull();
	}

	final public void unpack(MessageUnpackable obj) throws IOException, MessageTypeException {
		obj.messageUnpack(this);
	}

	//final public MessagePackObject unpack() throws IOException {
	//	return unpackObject();
	//}

	final public <T> T unpack(T to) throws IOException, MessageTypeException {
		return unpack((Class<T>)to.getClass(), to);
	}

	final public <T> T unpack(Class<T> klass) throws IOException, MessageTypeException {
		return unpack(klass, null);
	}

	final public <T> T unpack(Class<T> klass, T to) throws IOException, MessageTypeException {
		if(tryUnpackNull()) { return null; }
		return (T)TemplateRegistry.lookup(klass).unpack(this, to);
	}

	final public Object unpack(Template tmpl) throws IOException, MessageTypeException {
		return unpack(tmpl, null);
	}

	final public <T> T unpack(Template tmpl, T to) throws IOException, MessageTypeException {
		return (T)tmpl.unpack(this, to);
	}
}

