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

import java.io.IOException;
import java.nio.ByteBuffer;
import java.math.BigInteger;

abstract class BufferedUnpackerImpl extends UnpackerImpl {
	int offset = 0;
	int filled = 0;
	byte[] buffer = null;
	boolean bufferReferenced = false;  // TODO zero-copy buffer
	private ByteBuffer castBuffer = ByteBuffer.allocate(8);

	abstract boolean fill() throws IOException;

	final boolean next(UnpackResult result) throws IOException, UnpackException {
		if(filled == 0) {
			if(!fill()) {
				return false;
			}
		}

		do {
			int noffset = super.execute(buffer, offset, filled);
			if(noffset <= offset) {
				if(!fill()) {
					return false;
				}
				continue;
			}
			offset = noffset;
		} while(!super.isFinished());

		MessagePackObject obj = super.getData();
		super.reset();
		result.done(obj);

		return true;
	}

	private final void more(int require) throws IOException, UnpackException {
		while(filled - offset < require) {
			if(!fill()) {
				// FIXME
				throw new UnpackException("insufficient buffer");
			}
		}
	}

	private final boolean tryMore(int require) throws IOException, UnpackException {
		while(filled - offset < require) {
			if(!fill()) {
				return false;
			}
		}
		return true;
	}

	private final void advance(int length) {
		offset += length;
	}

	final byte unpackByte() throws IOException, MessageTypeException {
		int o = unpackInt();
		if(0x7f < o || o < -0x80) {
			throw new MessageTypeException();
		}
		return (byte)o;
	}

	final short unpackShort() throws IOException, MessageTypeException {
		int o = unpackInt();
		if(0x7fff < o || o < -0x8000) {
			throw new MessageTypeException();
		}
		return (short)o;
	}

	final int unpackInt() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		if((b & 0x80) == 0 || (b & 0xe0) == 0xe0) {  // Fixnum
			advance(1);
			return (int)b;
		}
		switch(b & 0xff) {
		case 0xcc:  // unsigned int  8
			more(2);
			advance(2);
			return (int)((short)(buffer[offset-1]) & 0xff);
		case 0xcd:  // unsigned int 16
			more(3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			advance(3);
			return (int)((int)castBuffer.getShort(0) & 0xffff);
		case 0xce:  // unsigned int 32
			more(5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			{
				int o = castBuffer.getInt(0);
				if(o < 0) {
					throw new MessageTypeException();
				}
				advance(5);
				return o;
			}
		case 0xcf:  // unsigned int 64
			more(9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			{
				long o = castBuffer.getLong(0);
				if(o < 0 || o > 0x7fffffffL) {
					throw new MessageTypeException();
				}
				advance(9);
				return (int)o;
			}
		case 0xd0:  // signed int  8
			more(2);
			advance(2);
			return (int)buffer[offset-1];
		case 0xd1:  // signed int 16
			more(3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			advance(3);
			return (int)castBuffer.getShort(0);
		case 0xd2:  // signed int 32
			more(4);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(4);
			return (int)castBuffer.getInt(0);
		case 0xd3:  // signed int 64
			more(9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			{
				long o = castBuffer.getLong(0);
				if(0x7fffffffL < o || o < -0x80000000L) {
					throw new MessageTypeException();
				}
				advance(9);
				return (int)o;
			}
		default:
			throw new MessageTypeException();
		}
	}

	final long unpackLong() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		if((b & 0x80) == 0 || (b & 0xe0) == 0xe0) {  // Fixnum
			advance(1);
			return (long)b;
		}
		switch(b & 0xff) {
		case 0xcc:  // unsigned int  8
			more(2);
			advance(2);
			return (long)((short)(buffer[offset-1]) & 0xff);
		case 0xcd:  // unsigned int 16
			more(3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			advance(3);
			return (long)((int)castBuffer.getShort(0) & 0xffff);
		case 0xce:  // unsigned int 32
			more(5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(5);
			return ((long)castBuffer.getInt(0) & 0xffffffffL);
		case 0xcf:  // unsigned int 64
			more(9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			{
				long o = castBuffer.getLong(0);
				if(o < 0) {
					throw new MessageTypeException();
				}
				advance(9);
				return o;
			}
		case 0xd0:  // signed int  8
			more(2);
			advance(2);
			return (long)buffer[offset-1];
		case 0xd1:  // signed int 16
			more(3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			advance(3);
			return (long)castBuffer.getShort(0);
		case 0xd2:  // signed int 32
			more(4);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(4);
			return (long)castBuffer.getInt(0);
		case 0xd3:  // signed int 64
			more(9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			advance(9);
			return (long)castBuffer.getLong(0);
		default:
			throw new MessageTypeException();
		}
	}

	final BigInteger unpackBigInteger() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		if((b & 0xff) != 0xcf) {
			return BigInteger.valueOf(unpackLong());
		}

		// unsigned int 64
		more(9);
		castBuffer.rewind();
		castBuffer.put(buffer, offset+1, 8);
		advance(9);
		long o = castBuffer.getLong(0);
		if(o < 0) {
			return new BigInteger(1, castBuffer.array());
		} else {
			return BigInteger.valueOf(o);
		}
	}

	final float unpackFloat() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		switch(b & 0xff) {
		case 0xca:  // float
			more(5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(5);
			return castBuffer.getFloat(0);
		case 0xcb:  // double
			more(9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			advance(9);
			// FIXME overflow check
			return (float)castBuffer.getDouble(0);
		default:
			throw new MessageTypeException();
		}
	}

	final double unpackDouble() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		switch(b & 0xff) {
		case 0xca:  // float
			more(5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(5);
			return (double)castBuffer.getFloat(0);
		case 0xcb:  // double
			more(9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			advance(9);
			return castBuffer.getDouble(0);
		default:
			throw new MessageTypeException();
		}
	}

	final Object unpackNull() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset] & 0xff;
		if(b != 0xc0) {  // nil
			throw new MessageTypeException();
		}
		advance(1);
		return null;
	}

	final boolean tryUnpackNull() throws IOException {
		if(!tryMore(1)) {
			return false;
		}
		int b = buffer[offset] & 0xff;
		if(b != 0xc0) {  // nil
			return false;
		}
		advance(1);
		return true;
	}

	final boolean unpackBoolean() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset] & 0xff;
		if(b == 0xc2) {  // false
			advance(1);
			return false;
		} else if(b == 0xc3) {  // true
			advance(1);
			return true;
		} else {
			throw new MessageTypeException();
		}
	}

	final int unpackArray() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		if((b & 0xf0) == 0x90) {  // FixArray
			advance(1);
			return (int)(b & 0x0f);
		}
		switch(b & 0xff) {
		case 0xdc:  // array 16
			more(3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			advance(3);
			return (int)castBuffer.getShort(0) & 0xffff;
		case 0xdd:  // array 32
			more(5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(5);
			// FIXME overflow check
			return castBuffer.getInt(0) & 0x7fffffff;
		default:
			throw new MessageTypeException();
		}
	}

	final int unpackMap() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		if((b & 0xf0) == 0x80) {  // FixMap
			advance(1);
			return (int)(b & 0x0f);
		}
		switch(b & 0xff) {
		case 0xde:  // map 16
			more(3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			advance(3);
			return (int)castBuffer.getShort(0) & 0xffff;
		case 0xdf:  // map 32
			more(5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(5);
			// FIXME overflow check
			return castBuffer.getInt(0) & 0x7fffffff;
		default:
			throw new MessageTypeException();
		}
	}

	final int unpackRaw() throws IOException, MessageTypeException {
		more(1);
		int b = buffer[offset];
		if((b & 0xe0) == 0xa0) {  // FixRaw
			advance(1);
			return (int)(b & 0x1f);
		}
		switch(b & 0xff) {
		case 0xda:  // raw 16
			more(3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			advance(3);
			return (int)castBuffer.getShort(0) & 0xffff;
		case 0xdb:  // raw 32
			more(5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			advance(5);
			// FIXME overflow check
			return castBuffer.getInt(0) & 0x7fffffff;
		default:
			throw new MessageTypeException();
		}
	}

	final byte[] unpackRawBody(int length) throws IOException {
		more(length);
		byte[] bytes = new byte[length];
		System.arraycopy(buffer, offset, bytes, 0, length);
		advance(length);
		return bytes;
	}

	final byte[] unpackByteArray() throws IOException, MessageTypeException {
		int length = unpackRaw();
		byte[] body = unpackRawBody(length);
		return body;
	}

	final ByteBuffer unpackByteBuffer() throws IOException, MessageTypeException {
		// TODO zero-copy buffer
		int length = unpackRaw();
		more(length);
		ByteBuffer buf = ByteBuffer.wrap(buffer, offset, length);
		bufferReferenced = true;  // TODO fix magical code
		advance(length);
		return buf;
	}

	final String unpackString() throws IOException, MessageTypeException {
		int length = unpackRaw();
		more(length);
		String s;
		try {
			s = new String(buffer, offset, length, "UTF-8");
		} catch (Exception e) {
			throw new MessageTypeException();
		}
		advance(length);
		return s;
	}

	final MessagePackObject unpackObject() throws IOException {
		UnpackResult result = new UnpackResult();
		if(!next(result)) {
			super.reset();
			throw new UnpackException("insufficient buffer");
		}
		return result.getData();
	}
}

