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

public abstract class IntegerType extends MessagePackObject {
	@Override
	public boolean isIntegerType() {
		return true;
	}

	public static IntegerType create(byte value) {
		return new ShortIntegerTypeIMPL((int)value);
	}

	public static IntegerType create(short value) {
		return new ShortIntegerTypeIMPL((int)value);
	}

	public static IntegerType create(int value) {
		return new ShortIntegerTypeIMPL(value);
	}

	public static IntegerType create(long value) {
		return new LongIntegerTypeIMPL(value);
	}

	public static IntegerType create(BigInteger value) {
		return new BigIntegerTypeIMPL(value);
	}
}

