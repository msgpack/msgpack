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

import java.io.OutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.math.BigInteger;

/**
 * Packer enables you to serialize objects into OutputStream.
 *
 * <pre>
 * // create a packer with output stream
 * Packer pk = new Packer(System.out);
 *
 * // store an object with pack() method.
 * pk.pack(1);
 *
 * // you can store String, List, Map, byte[] and primitive types.
 * pk.pack(new ArrayList());
 * </pre>
 *
 * You can serialize objects that implements {@link MessagePackable} interface.
 */
public class Packer {
	protected byte[] castBytes = new byte[9];
	protected ByteBuffer castBuffer = ByteBuffer.wrap(castBytes);
	protected OutputStream out;

	public Packer(OutputStream out) {
		this.out = out;
	}

	public Packer packByte(byte d) throws IOException {
		if(d < -(1<<5)) {
			castBytes[0] = (byte)0xd0;
			castBytes[1] = d;
			out.write(castBytes, 0, 2);
		} else {
			out.write(d);
		}
		return this;
	}

	public Packer packShort(short d) throws IOException {
		if(d < -(1<<5)) {
			if(d < -(1<<7)) {
				// signed 16
				castBytes[0] = (byte)0xd1;
				castBuffer.putShort(1, d);
				out.write(castBytes, 0, 3);
			} else {
				// signed 8
				castBytes[0] = (byte)0xd0;
				castBytes[1] = (byte)d;
				out.write(castBytes, 0, 2);
			}
		} else if(d < (1<<7)) {
			// fixnum
			out.write((byte)d);
		} else {
			if(d < (1<<8)) {
				// unsigned 8
				castBytes[0] = (byte)0xcc;
				castBytes[1] = (byte)d;
				out.write(castBytes, 0, 2);
			} else {
				// unsigned 16
				castBytes[0] = (byte)0xcd;
				castBuffer.putShort(1, d);
				out.write(castBytes, 0, 3);
			}
		}
		return this;
	}

	public Packer packInt(int d) throws IOException {
		if(d < -(1<<5)) {
			if(d < -(1<<15)) {
				// signed 32
				castBytes[0] = (byte)0xd2;
				castBuffer.putInt(1, d);
				out.write(castBytes, 0, 5);
			} else if(d < -(1<<7)) {
				// signed 16
				castBytes[0] = (byte)0xd1;
				castBuffer.putShort(1, (short)d);
				out.write(castBytes, 0, 3);
			} else {
				// signed 8
				castBytes[0] = (byte)0xd0;
				castBytes[1] = (byte)d;
				out.write(castBytes, 0, 2);
			}
		} else if(d < (1<<7)) {
			// fixnum
			out.write((byte)d);
		} else {
			if(d < (1<<8)) {
				// unsigned 8
				castBytes[0] = (byte)0xcc;
				castBytes[1] = (byte)d;
				out.write(castBytes, 0, 2);
			} else if(d < (1<<16)) {
				// unsigned 16
				castBytes[0] = (byte)0xcd;
				castBuffer.putShort(1, (short)d);
				out.write(castBytes, 0, 3);
			} else {
				// unsigned 32
				castBytes[0] = (byte)0xce;
				castBuffer.putInt(1, d);
				out.write(castBytes, 0, 5);
			}
		}
		return this;
	}

	public Packer packLong(long d) throws IOException {
		if(d < -(1L<<5)) {
			if(d < -(1L<<15)) {
				if(d < -(1L<<31)) {
					// signed 64
					castBytes[0] = (byte)0xd3;
					castBuffer.putLong(1, d);
					out.write(castBytes, 0, 9);
				} else {
					// signed 32
					castBytes[0] = (byte)0xd2;
					castBuffer.putInt(1, (int)d);
					out.write(castBytes, 0, 5);
				}
			} else {
				if(d < -(1<<7)) {
					// signed 16
					castBytes[0] = (byte)0xd1;
					castBuffer.putShort(1, (short)d);
					out.write(castBytes, 0, 3);
				} else {
					// signed 8
					castBytes[0] = (byte)0xd0;
					castBytes[1] = (byte)d;
					out.write(castBytes, 0, 2);
				}
			}
		} else if(d < (1<<7)) {
			// fixnum
			out.write((byte)d);
		} else {
			if(d < (1L<<16)) {
				if(d < (1<<8)) {
					// unsigned 8
					castBytes[0] = (byte)0xcc;
					castBytes[1] = (byte)d;
					out.write(castBytes, 0, 2);
				} else {
					// unsigned 16
					castBytes[0] = (byte)0xcd;
					castBuffer.putShort(1, (short)d);
					out.write(castBytes, 0, 3);
					//System.out.println("pack uint 16 "+(short)d);
				}
			} else {
				if(d < (1L<<32)) {
					// unsigned 32
					castBytes[0] = (byte)0xce;
					castBuffer.putInt(1, (int)d);
					out.write(castBytes, 0, 5);
				} else {
					// unsigned 64
					castBytes[0] = (byte)0xcf;
					castBuffer.putLong(1, d);
					out.write(castBytes, 0, 9);
				}
			}
		}
		return this;
	}

	public Packer packBigInteger(BigInteger d) throws IOException {
		if(d.bitLength() <= 63) {
			return packLong(d.longValue());
		} else if(d.bitLength() <= 64 && d.signum() >= 0) {
			castBytes[0] = (byte)0xcf;
			byte[] barray = d.toByteArray();
			castBytes[1] = barray[barray.length-8];
			castBytes[2] = barray[barray.length-7];
			castBytes[3] = barray[barray.length-6];
			castBytes[4] = barray[barray.length-5];
			castBytes[5] = barray[barray.length-4];
			castBytes[6] = barray[barray.length-3];
			castBytes[7] = barray[barray.length-2];
			castBytes[8] = barray[barray.length-1];
			out.write(castBytes);
			return this;
		} else {
			throw new MessageTypeException("can't BigInteger larger than 0xffffffffffffffff");
		}
	}

	public Packer packFloat(float d) throws IOException {
		castBytes[0] = (byte)0xca;
		castBuffer.putFloat(1, d);
		out.write(castBytes, 0, 5);
		return this;
	}

	public Packer packDouble(double d) throws IOException {
		castBytes[0] = (byte)0xcb;
		castBuffer.putDouble(1, d);
		out.write(castBytes, 0, 9);
		return this;
	}

	public Packer packNil() throws IOException {
		out.write((byte)0xc0);
		return this;
	}

	public Packer packTrue() throws IOException {
		out.write((byte)0xc3);
		return this;
	}

	public Packer packFalse() throws IOException {
		out.write((byte)0xc2);
		return this;
	}

	public Packer packBoolean(boolean d) throws IOException {
		return d ? packTrue() : packFalse();
	}

	public Packer packArray(int n) throws IOException {
		if(n < 16) {
			final int d = 0x90 | n;
			out.write((byte)d);
		} else if(n < 65536) {
			castBytes[0] = (byte)0xdc;
			castBuffer.putShort(1, (short)n);
			out.write(castBytes, 0, 3);
		} else {
			castBytes[0] = (byte)0xdd;
			castBuffer.putInt(1, n);
			out.write(castBytes, 0, 5);
		}
		return this;
	}

	public Packer packMap(int n) throws IOException {
		if(n < 16) {
			final int d = 0x80 | n;
			out.write((byte)d);
		} else if(n < 65536) {
			castBytes[0] = (byte)0xde;
			castBuffer.putShort(1, (short)n);
			out.write(castBytes, 0, 3);
		} else {
			castBytes[0] = (byte)0xdf;
			castBuffer.putInt(1, n);
			out.write(castBytes, 0, 5);
		}
		return this;
	}

	public Packer packRaw(int n) throws IOException {
		if(n < 32) {
			final int d = 0xa0 | n;
			out.write((byte)d);
		} else if(n < 65536) {
			castBytes[0] = (byte)0xda;
			castBuffer.putShort(1, (short)n);
			out.write(castBytes, 0, 3);
		} else {
			castBytes[0] = (byte)0xdb;
			castBuffer.putInt(1, n);
			out.write(castBytes, 0, 5);
		}
		return this;
	}

	public Packer packRawBody(byte[] b) throws IOException {
		out.write(b);
		return this;
	}

	public Packer packRawBody(byte[] b, int off, int length) throws IOException {
		out.write(b, off, length);
		return this;
	}


	public Packer packString(String s) throws IOException {
		byte[] b = ((String)s).getBytes("UTF-8");
		packRaw(b.length);
		return packRawBody(b);
	}


	public Packer pack(String o) throws IOException {
		if(o == null) { return packNil(); }
		return packString(o);
	}

	public Packer pack(MessagePackable o) throws IOException {
		if(o == null) { return packNil(); }
		o.messagePack(this);
		return this;
	}

	public Packer pack(byte[] o) throws IOException {
		if(o == null) { return packNil(); }
		packRaw(o.length);
		return packRawBody(o);
	}

	public Packer pack(List o) throws IOException {
		if(o == null) { return packNil(); }
		packArray(o.size());
		for(Object i : o) { pack(i); }
		return this;
	}

	@SuppressWarnings("unchecked")
	public Packer pack(Map o) throws IOException {
		if(o == null) { return packNil(); }
		packMap(o.size());
		for(Map.Entry e : ((Map<Object,Object>)o).entrySet()) {
			pack(e.getKey());
			pack(e.getValue());
		}
		return this;
	}

	public Packer pack(Boolean o) throws IOException {
		if(o == null) { return packNil(); }
		if(o) {
			return packTrue();
		} else {
			return packFalse();
		}
	}

	public Packer pack(Byte o) throws IOException {
		if(o == null) { return packNil(); }
		return packByte(o);
	}

	public Packer pack(Short o) throws IOException {
		if(o == null) { return packNil(); }
		return packShort(o);
	}

	public Packer pack(Integer o) throws IOException {
		if(o == null) { return packNil(); }
		return packInt(o);
	}

	public Packer pack(Long o) throws IOException {
		if(o == null) { return packNil(); }
		return packLong(o);
	}

	public Packer pack(Float o) throws IOException {
		if(o == null) { return packNil(); }
		return packFloat(o);
	}

	public Packer pack(Double o) throws IOException {
		if(o == null) { return packNil(); }
		return packDouble(o);
	}


	@SuppressWarnings("unchecked")
	public Packer pack(Object o) throws IOException {
		if(o == null) {
			return packNil();
		} else if(o instanceof String) {
			byte[] b = ((String)o).getBytes("UTF-8");
			packRaw(b.length);
			return packRawBody(b);
		} else if(o instanceof MessagePackable) {
			((MessagePackable)o).messagePack(this);
			return this;
		} else if(o instanceof byte[]) {
			byte[] b = (byte[])o;
			packRaw(b.length);
			return packRawBody(b);
		} else if(o instanceof List) {
			List<Object> l = (List<Object>)o;
			packArray(l.size());
			for(Object i : l) { pack(i); }
			return this;
		} else if(o instanceof Map) {
			Map<Object,Object> m = (Map<Object,Object>)o;
			packMap(m.size());
			for(Map.Entry e : m.entrySet()) {
				pack(e.getKey());
				pack(e.getValue());
			}
			return this;
		} else if(o instanceof Boolean) {
			if((Boolean)o) {
				return packTrue();
			} else {
				return packFalse();
			}
		} else if(o instanceof Integer) {
			return packInt((Integer)o);
		} else if(o instanceof Long) {
			return packLong((Long)o);
		} else if(o instanceof Short) {
			return packShort((Short)o);
		} else if(o instanceof Byte) {
			return packByte((Byte)o);
		} else if(o instanceof Float) {
			return packFloat((Float)o);
		} else if(o instanceof Double) {
			return packDouble((Double)o);
		} else if(o instanceof BigInteger) {
			return packBigInteger((BigInteger)o);
		} else {
			throw new MessageTypeException("unknown object "+o+" ("+o.getClass()+")");
		}
	}
}

