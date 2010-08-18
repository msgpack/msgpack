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

class BigIntegerTypeIMPL extends IntegerType {
	private BigInteger value;

	BigIntegerTypeIMPL(BigInteger value) {
		this.value = value;
	}

	@Override
	public byte asByte() {
		if(value.compareTo(BigInteger.valueOf((long)Byte.MAX_VALUE)) > 0) {
			throw new MessageTypeException("type error");
		}
		return value.byteValue();
	}

	@Override
	public short asShort() {
		if(value.compareTo(BigInteger.valueOf((long)Short.MAX_VALUE)) > 0) {
			throw new MessageTypeException("type error");
		}
		return value.shortValue();
	}

	@Override
	public int asInt() {
		if(value.compareTo(BigInteger.valueOf((long)Integer.MAX_VALUE)) > 0) {
			throw new MessageTypeException("type error");
		}
		return value.intValue();
	}

	@Override
	public long asLong() {
		if(value.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0) {
			throw new MessageTypeException("type error");
		}
		return value.longValue();
	}

	@Override
	public BigInteger asBigInteger() {
		return value;
	}

	@Override
	public byte byteValue() {
		return value.byteValue();
	}

	@Override
	public short shortValue() {
		return value.shortValue();
	}

	@Override
	public int intValue() {
		return value.intValue();
	}

	@Override
	public long longValue() {
		return value.longValue();
	}

	@Override
	public BigInteger bigIntegerValue() {
		return value;
	}

	@Override
	public float floatValue() {
		return value.floatValue();
	}

	@Override
	public double doubleValue() {
		return value.doubleValue();
	}

	@Override
	public void messagePack(Packer pk) throws IOException {
		pk.packBigInteger(value);
	}

	@Override
	public boolean equals(Object obj) {
		if(obj.getClass() != getClass()) {
			if(obj.getClass() == ShortIntegerTypeIMPL.class) {
				return BigInteger.valueOf(((ShortIntegerTypeIMPL)obj).longValue()).equals(value);
			} else if(obj.getClass() == LongIntegerTypeIMPL.class) {
				return BigInteger.valueOf(((LongIntegerTypeIMPL)obj).longValue()).equals(value);
			}
			return false;
		}
		return ((BigIntegerTypeIMPL)obj).value.equals(value);
	}

	@Override
	public int hashCode() {
		return value.hashCode();
	}

	@Override
	public Object clone() {
		return new BigIntegerTypeIMPL(value);
	}
}

