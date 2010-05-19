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

import java.nio.ByteBuffer;
//import java.math.BigInteger;
import org.msgpack.*;
import org.msgpack.schema.GenericSchema;
import org.msgpack.schema.IMapSchema;
import org.msgpack.schema.IArraySchema;

public class UnpackerImpl {
	static final int CS_HEADER      = 0x00;
	static final int CS_FLOAT       = 0x0a;
	static final int CS_DOUBLE      = 0x0b;
	static final int CS_UINT_8      = 0x0c;
	static final int CS_UINT_16     = 0x0d;
	static final int CS_UINT_32     = 0x0e;
	static final int CS_UINT_64     = 0x0f;
	static final int CS_INT_8       = 0x10;
	static final int CS_INT_16      = 0x11;
	static final int CS_INT_32      = 0x12;
	static final int CS_INT_64      = 0x13;
	static final int CS_RAW_16      = 0x1a;
	static final int CS_RAW_32      = 0x1b;
	static final int CS_ARRAY_16    = 0x1c;
	static final int CS_ARRAY_32    = 0x1d;
	static final int CS_MAP_16      = 0x1e;
	static final int CS_MAP_32      = 0x1f;
	static final int ACS_RAW_VALUE  = 0x20;
	static final int CT_ARRAY_ITEM  = 0x00;
	static final int CT_MAP_KEY     = 0x01;
	static final int CT_MAP_VALUE   = 0x02;

	static final int MAX_STACK_SIZE = 32;

	private int cs;
	private int trail;
	private int top;
	private int[]    stack_ct       = new int[MAX_STACK_SIZE];
	private int[]    stack_count    = new int[MAX_STACK_SIZE];
	private Object[] stack_obj      = new Object[MAX_STACK_SIZE];
	private Schema[] stack_schema   = new Schema[MAX_STACK_SIZE];
	private int top_ct;
	private int top_count;
	private Object top_obj;
	private Schema top_schema;
	private ByteBuffer castBuffer   = ByteBuffer.allocate(8);
	private boolean finished = false;
	private Object data = null;

	private static final Schema GENERIC_SCHEMA = new GenericSchema();
	private Schema rootSchema;

	public UnpackerImpl()
	{
		setSchema(GENERIC_SCHEMA);
	}

	public void setSchema(Schema schema)
	{
		this.rootSchema = schema;
		reset();
	}

	public final Object getData()
	{
		return data;
	}

	public final boolean isFinished()
	{
		return finished;
	}

	public final void resetState() {
		cs = CS_HEADER;
		top = -1;
		top_ct = 0;
		top_count = 0;
		top_obj = null;
		top_schema = rootSchema;
	}

	public final void reset()
	{
		resetState();
		finished = false;
		data = null;
	}

	@SuppressWarnings("unchecked")
	public final int execute(byte[] src, int off, int length) throws UnpackException
	{
		if(off >= length) { return off; }

		int limit = length;
		int i = off;
		int count;

		Object obj = null;

		_out: do {
		_header_again: {
			//System.out.println("while i:"+i+" limit:"+limit);

			int b = src[i];

			_push: {
				_fixed_trail_again:
				if(cs == CS_HEADER) {
	
					if((b & 0x80) == 0) {  // Positive Fixnum
						//System.out.println("positive fixnum "+b);
						obj = top_schema.createFromByte((byte)b);
						break _push;
					}
	
					if((b & 0xe0) == 0xe0) {  // Negative Fixnum
						//System.out.println("negative fixnum "+b);
						obj = top_schema.createFromByte((byte)b);
						break _push;
					}
	
					if((b & 0xe0) == 0xa0) {  // FixRaw
						trail = b & 0x1f;
						if(trail == 0) {
							obj = top_schema.createFromRaw(new byte[0], 0, 0);
							break _push;
						}
						cs = ACS_RAW_VALUE;
						break _fixed_trail_again;
					}
	
					if((b & 0xf0) == 0x90) {  // FixArray
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error");
						}
						if(!(top_schema instanceof IArraySchema)) {
							throw new RuntimeException("type error");
						}
						count = b & 0x0f;
						//System.out.println("fixarray count:"+count);
						obj = new Object[count];
						if(count == 0) { break _push; }  // FIXME check IArraySchema
						++top;
						stack_obj[top]    = top_obj;
						stack_ct[top]     = top_ct;
						stack_count[top]  = top_count;
						stack_schema[top] = top_schema;
						top_obj    = obj;
						top_ct     = CT_ARRAY_ITEM;
						top_count  = count;
						top_schema = ((IArraySchema)top_schema).getElementSchema(0);
						break _header_again;
					}
	
					if((b & 0xf0) == 0x80) {  // FixMap
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error");
						}
						if(!(top_schema instanceof IMapSchema)) {
							throw new RuntimeException("type error");
						}
						count = b & 0x0f;
						obj = new Object[count*2];
						if(count == 0) { break _push; }  // FIXME check IMapSchema
						//System.out.println("fixmap count:"+count);
						++top;
						stack_obj[top]    = top_obj;
						stack_ct[top]     = top_ct;
						stack_count[top]  = top_count;
						stack_schema[top] = top_schema;
						top_obj    = obj;
						top_ct     = CT_MAP_KEY;
						top_count  = count;
						top_schema = ((IMapSchema)top_schema).getKeySchema();
						break _header_again;
					}
	
					switch(b & 0xff) {    // FIXME
					case 0xc0:  // nil
						obj = top_schema.createFromNil();
						break _push;
					case 0xc2:  // false
						obj = top_schema.createFromBoolean(false);
						break _push;
					case 0xc3:  // true
						obj = top_schema.createFromBoolean(true);
						break _push;
					case 0xca:  // float
					case 0xcb:  // double
					case 0xcc:  // unsigned int  8
					case 0xcd:  // unsigned int 16
					case 0xce:  // unsigned int 32
					case 0xcf:  // unsigned int 64
					case 0xd0:  // signed int  8
					case 0xd1:  // signed int 16
					case 0xd2:  // signed int 32
					case 0xd3:  // signed int 64
						trail = 1 << (b & 0x03);
						cs = b & 0x1f;
						//System.out.println("a trail "+trail+"  cs:"+cs);
						break _fixed_trail_again;
					case 0xda:  // raw 16
					case 0xdb:  // raw 32
					case 0xdc:  // array 16
					case 0xdd:  // array 32
					case 0xde:  // map 16
					case 0xdf:  // map 32
						trail = 2 << (b & 0x01);
						cs = b & 0x1f;
						//System.out.println("b trail "+trail+"  cs:"+cs);
						break _fixed_trail_again;
					default:
						//System.out.println("unknown b "+(b&0xff));
						throw new UnpackException("parse error");
					}
	
				}  // _fixed_trail_again

				do {
				_fixed_trail_again: {
	
					if(limit - i <= trail) { break _out; }
					int n = i + 1;
					i += trail;

					switch(cs) {
					case CS_FLOAT:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						obj = top_schema.createFromFloat( castBuffer.getFloat(0) );
						//System.out.println("float "+obj);
						break _push;
					case CS_DOUBLE:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						obj = top_schema.createFromDouble( castBuffer.getDouble(0) );
						//System.out.println("double "+obj);
						break _push;
					case CS_UINT_8:
						//System.out.println(n);
						//System.out.println(src[n]);
						//System.out.println(src[n+1]);
						//System.out.println(src[n-1]);
						obj = top_schema.createFromShort( (short)((src[n]) & 0xff) );
						//System.out.println("uint8 "+obj);
						break _push;
					case CS_UINT_16:
						//System.out.println(src[n]);
						//System.out.println(src[n+1]);
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						obj = top_schema.createFromInt( ((int)castBuffer.getShort(0)) & 0xffff );
						//System.out.println("uint 16 "+obj);
						break _push;
					case CS_UINT_32:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						obj = top_schema.createFromLong( ((long)castBuffer.getInt(0)) & 0xffffffffL );
						//System.out.println("uint 32 "+obj);
						break _push;
					case CS_UINT_64:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						{
							long o = castBuffer.getLong(0);
							if(o < 0) {
								// FIXME
								//obj = GenericBigInteger.valueOf(o & 0x7fffffffL).setBit(31);
								throw new UnpackException("uint 64 bigger than 0x7fffffff is not supported");
							} else {
								obj = top_schema.createFromLong( o );
							}
						}
						break _push;
					case CS_INT_8:
						obj = top_schema.createFromByte(  src[n] );
						break _push;
					case CS_INT_16:
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						obj = top_schema.createFromShort( castBuffer.getShort(0) );
						break _push;
					case CS_INT_32:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						obj = top_schema.createFromInt( castBuffer.getInt(0) );
						break _push;
					case CS_INT_64:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						obj = top_schema.createFromLong( castBuffer.getLong(0) );
						break _push;
					case CS_RAW_16:
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						trail = ((int)castBuffer.getShort(0)) & 0xffff;
						if(trail == 0) {
							obj = top_schema.createFromRaw(new byte[0], 0, 0);
							break _push;
						}
						cs = ACS_RAW_VALUE;
						break _fixed_trail_again;
					case CS_RAW_32:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						// FIXME overflow check
						trail = castBuffer.getInt(0) & 0x7fffffff;
						if(trail == 0) {
							obj = top_schema.createFromRaw(new byte[0], 0, 0);
							break _push;
						}
						cs = ACS_RAW_VALUE;
					case ACS_RAW_VALUE:
						obj = top_schema.createFromRaw(src, n, trail);
						break _push;
					case CS_ARRAY_16:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error");
						}
						if(!(top_schema instanceof IArraySchema)) {
							throw new RuntimeException("type error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						count = ((int)castBuffer.getShort(0)) & 0xffff;
						obj = new Object[count];
						if(count == 0) { break _push; }  // FIXME check IArraySchema
						++top;
						stack_obj[top]    = top_obj;
						stack_ct[top]     = top_ct;
						stack_count[top]  = top_count;
						stack_schema[top] = top_schema;
						top_obj    = obj;
						top_ct     = CT_ARRAY_ITEM;
						top_count  = count;
						top_schema = ((IArraySchema)top_schema).getElementSchema(0);
						break _header_again;
					case CS_ARRAY_32:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error");
						}
						if(!(top_schema instanceof IArraySchema)) {
							throw new RuntimeException("type error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						// FIXME overflow check
						count = castBuffer.getInt(0) & 0x7fffffff;
						obj = new Object[count];
						if(count == 0) { break _push; }  // FIXME check IArraySchema
						++top;
						stack_obj[top]    = top_obj;
						stack_ct[top]     = top_ct;
						stack_count[top]  = top_count;
						stack_schema[top] = top_schema;
						top_obj    = obj;
						top_ct     = CT_ARRAY_ITEM;
						top_count  = count;
						top_schema = ((IArraySchema)top_schema).getElementSchema(0);
						break _header_again;
					case CS_MAP_16:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error");
						}
						if(!(top_schema instanceof IMapSchema)) {
							throw new RuntimeException("type error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						count = ((int)castBuffer.getShort(0)) & 0xffff;
						obj = new Object[count*2];
						if(count == 0) { break _push; }  // FIXME check IMapSchema
						//System.out.println("fixmap count:"+count);
						++top;
						stack_obj[top]    = top_obj;
						stack_ct[top]     = top_ct;
						stack_count[top]  = top_count;
						stack_schema[top] = top_schema;
						top_obj    = obj;
						top_ct     = CT_MAP_KEY;
						top_count  = count;
						top_schema = ((IMapSchema)top_schema).getKeySchema();
						break _header_again;
					case CS_MAP_32:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error");
						}
						if(!(top_schema instanceof IMapSchema)) {
							throw new RuntimeException("type error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						// FIXME overflow check
						count = castBuffer.getInt(0) & 0x7fffffff;
						obj = new Object[count*2];
						if(count == 0) { break _push; }  // FIXME check IMapSchema
						//System.out.println("fixmap count:"+count);
						++top;
						stack_obj[top]    = top_obj;
						stack_ct[top]     = top_ct;
						stack_count[top]  = top_count;
						stack_schema[top] = top_schema;
						top_obj    = obj;
						top_ct     = CT_MAP_KEY;
						top_count  = count;
						top_schema = ((IMapSchema)top_schema).getKeySchema();
						break _header_again;
					default:
						throw new UnpackException("parse error");
					}

				}  // _fixed_trail_again
				}  while(true);
			}  // _push

			do {
			_push: {
				//System.out.println("push top:"+top);
				if(top == -1) {
					++i;
					data = obj;
					finished = true;
					break _out;
				}

				switch(top_ct) {
				case CT_ARRAY_ITEM: {
						//System.out.println("array item "+obj);
						Object[] ar = (Object[])top_obj;
						ar[ar.length - top_count] = obj;
						if(--top_count == 0) {
							top_obj    = stack_obj[top];
							top_ct     = stack_ct[top];
							top_count  = stack_count[top];
							top_schema = stack_schema[top];
							obj = ((IArraySchema)top_schema).createFromArray(ar);
							stack_obj[top] = null;
							stack_schema[top] = null;
							--top;
							break _push;
						} else {
							top_schema = ((IArraySchema)stack_schema[top]).getElementSchema(ar.length - top_count);
						}
						break _header_again;
					}
				case CT_MAP_KEY: {
						//System.out.println("map key:"+top+" "+obj);
						Object[] mp = (Object[])top_obj;
						mp[mp.length - top_count*2] = obj;
						top_ct = CT_MAP_VALUE;
						top_schema = ((IMapSchema)stack_schema[top]).getValueSchema();
						break _header_again;
					}
				case CT_MAP_VALUE: {
						//System.out.println("map value:"+top+" "+obj);
						Object[] mp = (Object[])top_obj;
						mp[mp.length - top_count*2 + 1] = obj;
						if(--top_count == 0) {
							top_obj    = stack_obj[top];
							top_ct     = stack_ct[top];
							top_count  = stack_count[top];
							top_schema = stack_schema[top];
							obj = ((IMapSchema)top_schema).createFromMap(mp);
							stack_obj[top] = null;
							stack_schema[top] = null;
							--top;
							break _push;
						}
						top_ct = CT_MAP_KEY;
						break _header_again;
					}
				default:
					throw new UnpackException("parse error");
				}
			}  // _push
			} while(true);

		}  // _header_again
		cs = CS_HEADER;
		++i;
		} while(i < limit);  // _out

		return i;
	}
}

