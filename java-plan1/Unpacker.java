import java.io.*;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashMap;
import java.math.BigInteger;

public class Unpacker {
	protected static final int CS_HEADER      = 0x00;
	protected static final int CS_FLOAT       = 0x0a;
	protected static final int CS_DOUBLE      = 0x0b;
	protected static final int CS_UINT_8      = 0x0c;
	protected static final int CS_UINT_16     = 0x0d;
	protected static final int CS_UINT_32     = 0x0e;
	protected static final int CS_UINT_64     = 0x0f;
	protected static final int CS_INT_8       = 0x10;
	protected static final int CS_INT_16      = 0x11;
	protected static final int CS_INT_32      = 0x12;
	protected static final int CS_INT_64      = 0x13;
	protected static final int CS_RAW_16      = 0x1a;
	protected static final int CS_RAW_32      = 0x1b;
	protected static final int CS_ARRAY_16    = 0x1c;
	protected static final int CS_ARRAY_32    = 0x1d;
	protected static final int CS_MAP_16      = 0x1e;
	protected static final int CS_MAP_32      = 0x1f;
	protected static final int ACS_RAW_VALUE  = 0x20;
	protected static final int CT_ARRAY_ITEM  = 0x00;
	protected static final int CT_MAP_KEY     = 0x01;
	protected static final int CT_MAP_VALUE   = 0x02;

	protected static final int MAX_STACK_SIZE = 16;

	protected int cs    = CS_HEADER;
	protected int trail = 0;
	protected int top   = -1;
	protected boolean finished = false;
	protected int[]    stack_ct       = new int[MAX_STACK_SIZE];
	protected int[]    stack_count    = new int[MAX_STACK_SIZE];
	protected Object[] stack_obj      = new Object[MAX_STACK_SIZE];
	protected Object[] stack_map_key  = new Object[MAX_STACK_SIZE];
	//protected Object user;
	protected ByteBuffer castBuffer   = ByteBuffer.allocate(8);

	public Object getData()
	{
		return stack_obj[0];
	}

	public boolean isFinished()
	{
		return finished;
	}


	@SuppressWarnings("unchecked")
	public int execute(byte[] src, int off, int length) throws IOException
	{
		if(off >= length) { return off; }

		int limit = off + length;
		int i = off;
		int count;

		Object obj = null;

		_out: do {
		_header_again: {
			//System.out.println("while i:"+i);

			int b = src[i];

			_push: {
				_fixed_trail_again:
				if(cs == CS_HEADER) {
	
					if((b & 0x80) == 0) {  // Positive Fixnum
						//System.out.println("positive fixnum "+b);
						obj = b;
						break _push;
					}
	
					if((b & 0xe0) == 0xe0) {  // Negative Fixnum
						//System.out.println("negative fixnum "+b);
						obj = b;
						break _push;
					}
	
					if((b & 0xe0) == 0xa0) {  // FixRaw
						trail = b & 0x1f;
						if(trail == 0) {
							obj = new byte[0];
							break _push;
						}
						cs = ACS_RAW_VALUE;
						break _fixed_trail_again;
					}
	
					if((b & 0xf0) == 0x90) {  // FixArray
						if(top >= MAX_STACK_SIZE) {
							throw new IOException("parse error");
						}
						count = b & 0x0f;
						++top;
						stack_obj[top] = new ArrayList(count);
						stack_ct[top] = CT_ARRAY_ITEM;
						stack_count[top] = count;
						//System.out.println("fixarray count:"+count);
						break _header_again;
					}
	
					if((b & 0xf0) == 0x80) {  // FixMap
						if(top >= MAX_STACK_SIZE) {
							throw new IOException("parse error");
						}
						count = b & 0x0f;
						++top;
						stack_obj[top] = new HashMap(count);
						stack_ct[top] = CT_MAP_KEY;
						stack_count[top] = count;
						//System.out.println("fixmap count:"+count);
						break _header_again;
					}
	
					switch(b & 0xff) {    // FIXME
					case 0xc0:  // nil
						obj = null;
						break _push;
					case 0xc2:  // false
						obj = false;
						break _push;
					case 0xc3:  // true
						obj = true;
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
						throw new IOException("parse error");
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
						obj = castBuffer.getFloat(0);
						//System.out.println("float "+obj);
						break _push;
					case CS_DOUBLE:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						obj = castBuffer.getDouble(0);
						//System.out.println("double "+obj);
						break _push;
					case CS_UINT_8:
						//System.out.println(n);
						//System.out.println(src[n]);
						//System.out.println(src[n+1]);
						//System.out.println(src[n-1]);
						obj = ((int)src[n]) & 0xff;
						//System.out.println("uint8 "+obj);
						break _push;
					case CS_UINT_16:
						//System.out.println(src[n]);
						//System.out.println(src[n+1]);
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						obj = ((int)castBuffer.getShort(0)) & 0xffff;
						//System.out.println("uint 16 "+obj);
						break _push;
					case CS_UINT_32:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						{
							// FIXME always long?
							int o = castBuffer.getInt(0);
							if(o < 0) {
								obj = ((long)o) & 0xffffffffL;
							} else {
								obj = o;
							}
						}
						//System.out.println("uint 32 "+obj);
						break _push;
					case CS_UINT_64:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						{
							// FIXME always BigInteger?
							long o = castBuffer.getLong(0);
							if(o < 0) {
								obj = BigInteger.valueOf(o & 0x7fffffffL).setBit(31);
							} else {
								obj = o;
							}
						}
						throw new IOException("uint 64 is not supported");
					case CS_INT_8:
						obj = (int)src[n];
						break _push;
					case CS_INT_16:
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						obj = (int)castBuffer.getShort(0);
						break _push;
					case CS_INT_32:
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						obj = (int)castBuffer.getInt(0);
						break _push;
					case CS_INT_64:
						castBuffer.rewind();
						castBuffer.put(src, n, 8);
						{
							// FIXME always long?
							long o = castBuffer.getLong(0);
							if(o <= 0x7fffffffL && o > -0x80000000L) {
								obj = (int)o;
							} else {
								obj = o;
							}
						}
						//System.out.println("long "+obj);
						break _push;
					case CS_RAW_16:
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						trail = ((int)castBuffer.getShort(0)) & 0xffff;
						if(trail == 0) {
							obj = new byte[0];
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
							obj = new byte[0];
							break _push;
						}
						cs = ACS_RAW_VALUE;
					case ACS_RAW_VALUE:
						obj = ByteBuffer.wrap(src, n, trail);  // FIXME プール? コピー
						break _push;
					case CS_ARRAY_16:
						if(top >= MAX_STACK_SIZE) {
							throw new IOException("parse error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						count = ((int)castBuffer.getShort(0)) & 0xffff;
						++top;
						stack_obj[top] = new ArrayList(count);
						stack_ct[top] = CT_ARRAY_ITEM;
						stack_count[top] = count;
						break _header_again;
					case CS_ARRAY_32:
						if(top >= MAX_STACK_SIZE) {
							throw new IOException("parse error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						// FIXME overflow check
						count = castBuffer.getInt(0) & 0x7fffffff;
						++top;
						stack_obj[top] = new ArrayList(count);
						stack_ct[top] = CT_ARRAY_ITEM;
						stack_count[top] = count;
						break _header_again;
					case CS_MAP_16:
						if(top >= MAX_STACK_SIZE) {
							throw new IOException("parse error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 2);
						count = ((int)castBuffer.getShort(0)) & 0xffff;
						++top;
						stack_obj[top] = new HashMap(count);
						stack_ct[top] = CT_MAP_KEY;
						stack_count[top] = count;
						//System.out.println("fixmap count:"+count);
						break _header_again;
					case CS_MAP_32:
						if(top >= MAX_STACK_SIZE) {
							throw new IOException("parse error");
						}
						castBuffer.rewind();
						castBuffer.put(src, n, 4);
						// FIXME overflow check
						count = castBuffer.getInt(0) & 0x7fffffff;
						++top;
						stack_obj[top] = new HashMap(count);
						stack_ct[top] = CT_MAP_KEY;
						stack_count[top] = count;
						//System.out.println("fixmap count:"+count);
						break _header_again;
					default:
						throw new IOException("parse error");
					}

				}  // _fixed_trail_again
				}  while(true);
			}  // _push

			do {
			_push: {
				//System.out.println("push top:"+top);
				if(top == -1) {
					stack_obj[0] = obj;
					finished = true;
					break _out;
				}

				switch(stack_ct[top]) {
				case CT_ARRAY_ITEM:
					//System.out.println("array item "+obj);
					((ArrayList)(stack_obj[top])).add(obj);
					if(--stack_count[top] == 0) {
						obj = stack_obj[top];
						--top;
						break _push;
					}
					break _header_again;
				case CT_MAP_KEY:
					//System.out.println("map key:"+top+" "+obj);
					stack_map_key[top] = obj;
					stack_ct[top] = CT_MAP_VALUE;
					break _header_again;
				case CT_MAP_VALUE:
					//System.out.println("map value:"+top+" "+obj);
					((HashMap)(stack_obj[top])).put(stack_map_key[top], obj);
					if(--stack_count[top] == 0) {
						obj = stack_obj[top];
						--top;
						break _push;
					}
					stack_ct[top] = CT_MAP_KEY;
					break _header_again;
				default:
					throw new IOException("parse error");
				}
			}  // _push
			} while(true);

		}  // _header_again
		cs = CS_HEADER;
		++i;
		} while(i < limit);  // _out

		return i - off;
	}
}

