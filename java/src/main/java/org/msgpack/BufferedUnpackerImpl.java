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
//import java.math.BigInteger;

abstract class BufferedUnpackerImpl extends UnpackerImpl {
	int filled = 0;
	byte[] buffer = null;
	private ByteBuffer castBuffer = ByteBuffer.allocate(8);

	abstract boolean fill() throws IOException;

	final int next(int offset, UnpackResult result) throws IOException, UnpackException {
		if(filled == 0) {
			if(!fill()) {
				return offset;
			}
		}

		do {
			int noffset = super.execute(buffer, offset, filled);
			if(noffset <= offset) {
				if(!fill()) {
					return offset;
				}
			}
			offset = noffset;
		} while(!super.isFinished());

		Object obj = super.getData();
		super.reset();
		result.done(obj);

		return offset;
	}

	private final void more(int offset, int require) throws IOException, UnpackException {
		while(filled - offset < require) {
			if(!fill()) {
				// FIXME
				throw new UnpackException("insufficient buffer");
			}
		}
	}

	final byte unpackByte(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		int o = unpackInt(c, offset);
		if(0x7f < o || o < -0x80) {
			throw new MessageTypeException();
		}
		return (byte)o;
	}

	final short unpackShort(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		int o = unpackInt(c, offset);
		if(0x7fff < o || o < -0x8000) {
			throw new MessageTypeException();
		}
		return (short)o;
	}

	final int unpackInt(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset];
		if((b & 0x80) == 0 || (b & 0xe0) == 0xe0) {  // Fixnum
			return (int)b;
		}
		switch(b & 0xff) {
		case 0xcc:  // unsigned int  8
			more(offset, 2);
			c.advance(2);
			return (int)((short)buffer[offset+1] & 0xff);
		case 0xcd:  // unsigned int 16
			more(offset, 3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			c.advance(3);
			return (int)((int)castBuffer.getShort(0) & 0xffff);
		case 0xce:  // unsigned int 32
			more(offset, 5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			{
				int o = castBuffer.getInt(0);
				if(o < 0) {
					throw new MessageTypeException();
				}
				c.advance(5);
				return o;
			}
		case 0xcf:  // unsigned int 64
			more(offset, 9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			{
				long o = castBuffer.getLong(0);
				if(o < 0 || o > 0x7fffffffL) {
					throw new MessageTypeException();
				}
				c.advance(9);
				return (int)o;
			}
		case 0xd0:  // signed int  8
			more(offset, 2);
			c.advance(2);
			return (int)buffer[offset+1];
		case 0xd1:  // signed int 16
			more(offset, 3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			c.advance(3);
			return (int)castBuffer.getShort(0);
		case 0xd2:  // signed int 32
			more(offset, 4);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(4);
			return (int)castBuffer.getInt(0);
		case 0xd3:  // signed int 64
			more(offset, 9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			{
				long o = castBuffer.getLong(0);
				if(0x7fffffffL < o || o < -0x80000000L) {
					throw new MessageTypeException();
				}
				c.advance(9);
				return (int)o;
			}
		default:
			throw new MessageTypeException();
		}
	}

	final long unpackLong(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset];
		if((b & 0x80) == 0 || (b & 0xe0) == 0xe0) {  // Fixnum
			return (long)b;
		}
		switch(b & 0xff) {
		case 0xcc:  // unsigned int  8
			more(offset, 2);
			c.advance(2);
			return (long)((short)buffer[offset+1] & 0xff);
		case 0xcd:  // unsigned int 16
			more(offset, 3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			c.advance(3);
			return (long)((int)castBuffer.getShort(0) & 0xffff);
		case 0xce:  // unsigned int 32
			more(offset, 5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(5);
			return ((long)castBuffer.getInt(0) & 0xffffffffL);
		case 0xcf:  // unsigned int 64
			more(offset, 9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			{
				long o = castBuffer.getLong(0);
				if(o < 0) {
					// FIXME
					throw new MessageTypeException("uint 64 bigger than 0x7fffffff is not supported");
				}
				c.advance(9);
				return o;
			}
		case 0xd0:  // signed int  8
			more(offset, 2);
			c.advance(2);
			return (long)buffer[offset+1];
		case 0xd1:  // signed int 16
			more(offset, 3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			c.advance(3);
			return (long)castBuffer.getShort(0);
		case 0xd2:  // signed int 32
			more(offset, 4);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(4);
			return (long)castBuffer.getInt(0);
		case 0xd3:  // signed int 64
			more(offset, 9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			c.advance(9);
			return (long)castBuffer.getLong(0);
		default:
			throw new MessageTypeException();
		}
	}

	final float unpackFloat(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset];
		switch(b & 0xff) {
		case 0xca:  // float
			more(offset, 5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(5);
			return castBuffer.getFloat(0);
		case 0xcb:  // double
			more(offset, 9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			c.advance(9);
			// FIXME overflow check
			return (float)castBuffer.getDouble(0);
		default:
			throw new MessageTypeException();
		}
	}

	final double unpackDouble(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset];
		switch(b & 0xff) {
		case 0xca:  // float
			more(offset, 5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(5);
			return (double)castBuffer.getFloat(0);
		case 0xcb:  // double
			more(offset, 9);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 8);
			c.advance(9);
			return castBuffer.getDouble(0);
		default:
			throw new MessageTypeException();
		}
	}

	final Object unpackNull(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset] & 0xff;
		if(b != 0xc0) {  // nil
			throw new MessageTypeException();
		}
		c.advance(1);
		return null;
	}

	final boolean unpackBoolean(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset] & 0xff;
		if(b == 0xc2) {  // false
			c.advance(1);
			return false;
		} else if(b == 0xc3) {  // true
			c.advance(1);
			return true;
		} else {
			throw new MessageTypeException();
		}
	}

	final int unpackArray(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset];
		if((b & 0xf0) == 0x90) {  // FixArray
			c.advance(1);
			return (int)(b & 0x0f);
		}
		switch(b & 0xff) {
		case 0xdc:  // array 16
			more(offset, 3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			c.advance(3);
			return (int)castBuffer.getShort(0) & 0xffff;
		case 0xdd:  // array 32
			more(offset, 5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(5);
			// FIXME overflow check
			return castBuffer.getInt(0) & 0x7fffffff;
		default:
			throw new MessageTypeException();
		}
	}

	final int unpackMap(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset];
		if((b & 0xf0) == 0x80) {  // FixMap
			c.advance(1);
			return (int)(b & 0x0f);
		}
		switch(b & 0xff) {
		case 0xde:  // map 16
			more(offset, 3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			c.advance(3);
			return (int)castBuffer.getShort(0) & 0xffff;
		case 0xdf:  // map 32
			more(offset, 5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(5);
			// FIXME overflow check
			return castBuffer.getInt(0) & 0x7fffffff;
		default:
			throw new MessageTypeException();
		}
	}

	final int unpackRaw(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		more(offset, 1);
		int b = buffer[offset];
		if((b & 0xe0) == 0xa0) {  // FixRaw
			c.advance(1);
			return (int)(b & 0x0f);
		}
		switch(b & 0xff) {
		case 0xda:  // raw 16
			more(offset, 3);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 2);
			c.advance(3);
			return (int)castBuffer.getShort(0) & 0xffff;
		case 0xdb:  // raw 32
			more(offset, 5);
			castBuffer.rewind();
			castBuffer.put(buffer, offset+1, 4);
			c.advance(5);
			// FIXME overflow check
			return castBuffer.getInt(0) & 0x7fffffff;
		default:
			throw new MessageTypeException();
		}
	}

	final byte[] unpackRawBody(UnpackCursor c, int offset, int length) throws IOException, MessageTypeException {
		more(offset, length);
		byte[] bytes = new byte[length];
		System.arraycopy(buffer, offset, bytes, 0, length);
		c.advance(length);
		return bytes;
	}

	final String unpackString(UnpackCursor c, int offset) throws IOException, MessageTypeException {
		int length = unpackRaw(c, offset);
		offset = c.getOffset();
		more(offset, length);
		String s;
		try {
			s = new String(buffer, offset, length, "UTF-8");
		} catch (Exception e) {
			throw new MessageTypeException();
		}
		c.advance(length);
		return s;
	}
}

