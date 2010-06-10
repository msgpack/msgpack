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
package org.msgpack.schema;

import java.io.IOException;
import org.msgpack.*;

public class IntSchema extends Schema {
	public IntSchema() { }

	@Override
	public String getClassName() {
		return "Integer";
	}

	@Override
	public String getExpression() {
		return "int";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException {
		if(obj instanceof Number) {
			int value = ((Number)obj).intValue();
			if(value >= Short.MAX_VALUE) {
				long lvalue = ((Number)obj).longValue();
				if(lvalue > Integer.MAX_VALUE) {
					throw new MessageTypeException();
				}
			}
			pk.packInt(value);
		} else if(obj == null) {
			pk.packNil();
		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	public static final int convertInt(Object obj) throws MessageTypeException {
		if(obj instanceof Number) {
			int value = ((Number)obj).intValue();
			if(value >= Integer.MAX_VALUE) {
				long lvalue = ((Number)obj).longValue();
				if(lvalue > Integer.MAX_VALUE) {
					throw new MessageTypeException();
				}
			}
			return value;
		}
		throw new MessageTypeException();
	}

	@Override
	public Object convert(Object obj) throws MessageTypeException {
		return convertInt(obj);
	}

	@Override
	public Object createFromByte(byte v) {
		return (int)v;
	}

	@Override
	public Object createFromShort(short v) {
		return (int)v;
	}

	@Override
	public Object createFromInt(int v) {
		return (int)v;
	}

	@Override
	public Object createFromLong(long v) {
		if(v > Integer.MAX_VALUE) {
			throw new MessageTypeException();
		}
		return (int)v;
	}
}

