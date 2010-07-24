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
import org.msgpack.*;

class BigIntegerTypeIMPL extends IntegerType {
	private BigInteger value;

	BigIntegerTypeIMPL(BigInteger vlaue) {
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
	public float floatValue() {
		return value.floatValue();
	}

	@Override
	public double doubleValue() {
		return value.doubleValue();
	}
}

