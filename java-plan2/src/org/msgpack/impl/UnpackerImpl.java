package org.msgpack.impl;

import java.nio.ByteBuffer;
//import java.math.BigInteger;
import org.msgpack.UnpackException;

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

	static final int MAX_STACK_SIZE = 16;

	protected int cs    = CS_HEADER;
	protected int trail = 0;
	protected int top   = -1;
	protected boolean finished = false;
	protected Object data = null;
	protected int[]    stack_ct       = new int[MAX_STACK_SIZE];
	protected int[]    stack_count    = new int[MAX_STACK_SIZE];
	protected Object[] stack_obj      = new Object[MAX_STACK_SIZE];
	protected ByteBuffer castBuffer   = ByteBuffer.allocate(8);
	protected ObjectBuilder builder;

	protected UnpackerImpl(ObjectBuilder builder)
	{
		this.builder = builder;
	}

	protected void setBuilder(ObjectBuilder builder)
	{
		this.builder = builder;
	}

	protected Object getData()
	{
		return data;
	}

	protected boolean isFinished()
	{
		return finished;
	}

	protected void reset()
	{
		for(int i=0; i <= top; ++top) {
			stack_ct[top] = 0;
			stack_count[top] = 0;
			stack_obj[top] = null;
		}
		cs = CS_HEADER;
		trail = 0;
		top = -1;
		finished = false;
		data = null;
	}

	@SuppressWarnings("unchecked")
	protected int execute(byte[] src, int off, int length) throws UnpackException
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
						obj = builder.createByte((byte)b);
						break _push;
					}
	
					if((b & 0xe0) == 0xe0) {  // Negative Fixnum
						//System.out.println("negative fixnum "+b);
						obj = builder.createByte((byte)b);
						break _push;
					}
	
					if((b & 0xe0) == 0xa0) {  // FixRaw
						trail = b & 0x1f;
						if(trail == 0) {
							obj = builder.createRaw(new byte[0], 0, 0);
							break _push;
						}
						cs = ACS_RAW_VALUE;
						break _fixed_trail_again;
					}
	
					if((b & 0xf0) == 0x90) {  // FixArray
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
						}
						count = b & 0x0f;
						++top;
						stack_obj[top] = builder.createArray(count);
						stack_ct[top] = CT_ARRAY_ITEM;
						stack_count[top] = count;
						//System.out.println("fixarray count:"+count);
						break _header_again;
					}
	
					if((b & 0xf0) == 0x80) {  // FixMap
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
						}
						count = b & 0x0f;
						++top;
						stack_obj[top] = builder.createMap(count);
						stack_ct[top] = CT_MAP_KEY;
						stack_count[top] = count;
						//System.out.println("fixmap count:"+count);
						break _header_again;
					}
	
					switch(b & 0xff) {    // FIXME
					case 0xc0:  // nil
						obj = builder.createNil();
						break _push;
					case 0xc2:  // false
						obj = builder.createBoolean(false);
						break _push;
					case 0xc3:  // true
						obj = builder.createBoolean(true);
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
						throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
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
						obj = builder.createFloat( castBuffer.getFloat(0) );
						//System.out.println("float "+obj);
						break _push;
					case CS_DOUBLE:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						obj = builder.createDouble( castBuffer.getDouble(0) );
						//System.out.println("double "+obj);
						break _push;
					case CS_UINT_8:
						//System.out.println(n);
						//System.out.println(src[n]);
						//System.out.println(src[n+1]);
						//System.out.println(src[n-1]);
						obj = builder.createShort( (short)((src[n]) & 0xff) );
						//System.out.println("uint8 "+obj);
						break _push;
					case CS_UINT_16:
						//System.out.println(src[n]);
						//System.out.println(src[n+1]);
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						obj = builder.createInt( ((int)castBuffer.getShort(0)) & 0xffff );
						//System.out.println("uint 16 "+obj);
						break _push;
					case CS_UINT_32:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						obj = builder.createLong( ((long)castBuffer.getInt(0)) & 0xffffffffL );
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
							} else {
								obj = builder.createLong( o );
							}
						}
						throw new UnpackException("uint 64 bigger than 0x7fffffff is not supported", UnpackException.PARSE_ERROR);
					case CS_INT_8:
						obj = builder.createByte(  src[n] );
						break _push;
					case CS_INT_16:
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						obj = builder.createShort( castBuffer.getShort(0) );
						break _push;
					case CS_INT_32:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						obj = builder.createInt( castBuffer.getInt(0) );
						break _push;
					case CS_INT_64:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						obj = builder.createLong( castBuffer.getLong(0) );
						break _push;
					case CS_RAW_16:
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						trail = ((int)castBuffer.getShort(0)) & 0xffff;
						if(trail == 0) {
							obj = builder.createRaw(new byte[0], 0, 0);
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
							obj = builder.createRaw(new byte[0], 0, 0);
							break _push;
						}
						cs = ACS_RAW_VALUE;
					case ACS_RAW_VALUE:
						obj = builder.createRaw(src, n, trail);
						break _push;
					case CS_ARRAY_16:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						count = ((int)castBuffer.getShort(0)) & 0xffff;
						++top;
						stack_obj[top] = builder.createArray(count);
						stack_ct[top] = CT_ARRAY_ITEM;
						stack_count[top] = count;
						break _header_again;
					case CS_ARRAY_32:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						// FIXME overflow check
						count = castBuffer.getInt(0) & 0x7fffffff;
						++top;
						stack_obj[top] = builder.createArray(count);
						stack_ct[top] = CT_ARRAY_ITEM;
						stack_count[top] = count;
						break _header_again;
					case CS_MAP_16:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						count = ((int)castBuffer.getShort(0)) & 0xffff;
						++top;
						stack_obj[top] = builder.createMap(count);
						stack_ct[top] = CT_MAP_KEY;
						stack_count[top] = count;
						//System.out.println("fixmap count:"+count);
						break _header_again;
					case CS_MAP_32:
						if(top >= MAX_STACK_SIZE) {
							throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						// FIXME overflow check
						count = castBuffer.getInt(0) & 0x7fffffff;
						++top;
						stack_obj[top] = builder.createMap(count);
						stack_ct[top] = CT_MAP_KEY;
						stack_count[top] = count;
						//System.out.println("fixmap count:"+count);
						break _header_again;
					default:
						throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
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

				switch(stack_ct[top]) {
				case CT_ARRAY_ITEM:
					//System.out.println("array item "+obj);
					((ArrayBuilder)stack_obj[top]).add(obj);
					if(--stack_count[top] == 0) {
						obj = ((ArrayBuilder)stack_obj[top]).finish();
						stack_obj[top] = null;
						--top;
						break _push;
					}
					break _header_again;
				case CT_MAP_KEY:
					//System.out.println("map key:"+top+" "+obj);
					MapBuilder mb = (MapBuilder)stack_obj[top];
					mb.putKey(obj);
					stack_ct[top] = CT_MAP_VALUE;
					break _header_again;
				case CT_MAP_VALUE:
					//System.out.println("map value:"+top+" "+obj);
					((MapBuilder)stack_obj[top]).putValue(obj);
					if(--stack_count[top] == 0) {
						obj = ((MapBuilder)stack_obj[top]).finish();
						stack_obj[top] = null;
						--top;
						break _push;
					}
					stack_ct[top] = CT_MAP_KEY;
					break _header_again;
				default:
					throw new UnpackException("parse error", UnpackException.PARSE_ERROR);
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

