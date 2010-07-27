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

class DoubleTypeIMPL extends FloatType {
	private double value;

	public DoubleTypeIMPL(double value) {
		this.value = value;
	}

	@Override
	public float asFloat() {
		// FIXME check overflow, underflow?
		return (float)value;
	}

	@Override
	public double asDouble() {
		return value;
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
	public float floatValue() {
		return (float)value;
	}

	@Override
	public double doubleValue() {
		return (double)value;
	}

	@Override
	public void messagePack(Packer pk) throws IOException {
		pk.packDouble(value);
	}

	@Override
	public boolean equals(Object obj) {
		if(obj.getClass() != getClass()) {
			return false;
		}
		return ((DoubleTypeIMPL)obj).value == value;
	}

	@Override
	public Object clone() {
		return new DoubleTypeIMPL(value);
	}
}

