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
package org.msgpack.object;

import java.math.BigInteger;
import java.io.IOException;
import org.msgpack.*;

class LongIntegerTypeIMPL extends IntegerType {
	private long value;

	LongIntegerTypeIMPL(long value) {
		this.value = value;
	}

	@Override
	public byte asByte() {
		if(value > (long)Byte.MAX_VALUE) {
			throw new MessageTypeException("type error");
		}
		return (byte)value;
	}

	@Override
	public short asShort() {
		if(value > (long)Short.MAX_VALUE) {
			throw new MessageTypeException("type error");
		}
		return (short)value;
	}

	@Override
	public int asInt() {
		if(value > (long)Integer.MAX_VALUE) {
			throw new MessageTypeException("type error");
		}
		return (int)value;
	}

	@Override
	public long asLong() {
		return value;
	}

	@Override
	public BigInteger asBigInteger() {
		return BigInteger.valueOf(value);
	}

	@Override
	public byte byteValue() {
		return (byte)value;
	}

	@Override
	public short shortValue() {
		return (short)value;
	}

	@Override
	public int intValue() {
		return (int)value;
	}

	@Override
	public long longValue() {
		return (long)value;
	}

	@Override
	public BigInteger bigIntegerValue() {
		return BigInteger.valueOf(value);
	}

	@Override
	public float floatValue() {
		return (float)value;
	}

	@Override
	public double doubleValue() {
		return (double)value;
	}

	@Override
	public void messagePack(Packer pk) throws IOException {
		pk.packLong(value);
	}

	@Override
	public boolean equals(Object obj) {
		if(obj.getClass() != getClass()) {
			if(obj.getClass() == ShortIntegerTypeIMPL.class) {
				return value == ((ShortIntegerTypeIMPL)obj).longValue();
			} else if(obj.getClass() == BigIntegerTypeIMPL.class) {
				return (long)value == ((BigIntegerTypeIMPL)obj).longValue();
			}
			return false;
		}
		return ((LongIntegerTypeIMPL)obj).value == value;
	}

	@Override
	public int hashCode() {
		return (int)(value^(value>>>32));
	}

	@Override
	public Object clone() {
		return new LongIntegerTypeIMPL(value);
	}
}

