//
// MessagePack for Java
//
// Copyright (C) 2009 FURUHASHI Sadayuki
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

import java.util.Arrays;
import java.util.List;
import java.util.HashMap;
import java.io.IOException;
import org.msgpack.*;
//import org.msgpack.generic.*;

public class GenericSchema extends Schema implements IArraySchema, IMapSchema {
	public GenericSchema() {
		super("Object");
	}

	@Override
	public String getExpression() {
		return "object";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException {
		pk.pack(obj);
	}

	@Override
	public Object convert(Object obj) throws MessageTypeException {
		return obj;
	}

	@Override
	public Schema getElementSchema(int index) {
		return this;
	}

	@Override
	public Schema getKeySchema() {
		return this;
	}

	@Override
	public Schema getValueSchema() {
		return this;
	}

	@Override
	public Object createFromNil() {
		return null;
	}

	@Override
	public Object createFromBoolean(boolean v) {
		return v;
	}

	@Override
	public Object createFromByte(byte v) {
		return v;
	}

	@Override
	public Object createFromShort(short v) {
		return v;
	}

	@Override
	public Object createFromInt(int v) {
		return v;
	}

	@Override
	public Object createFromLong(long v) {
		return v;
	}

	@Override
	public Object createFromFloat(float v) {
		return v;
	}

	@Override
	public Object createFromDouble(double v) {
		return v;
	}

	@Override
	public Object createFromRaw(byte[] b, int offset, int length) {
		byte[] bytes = new byte[length];
		System.arraycopy(b, offset, bytes, 0, length);
		return bytes;
	}

	@Override
	public Object createFromArray(Object[] obj) {
		return Arrays.asList(obj);
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object createFromMap(Object[] obj) {
		HashMap m = new HashMap(obj.length / 2);
		int i = 0;
		while(i < obj.length) {
			Object k = obj[i++];
			Object v = obj[i++];
			m.put(k, v);
		}
		return m;
	}

	/*
   @Override
	public Object createFromNil() {
		return null;
	}

	@Override
	public Object createFromBoolean(boolean v) {
		return new GenericBoolean(v);
	}

	@Override
	public Object createFromFromByte(byte v) {
		return new GenericByte(v);
	}

	@Override
	public Object createFromShort(short v) {
		return new GenericShort(v);
	}

	@Override
	public Object createFromInt(int v) {
		return new GenericInt(v);
	}

	@Override
	public Object createFromLong(long v) {
		return new GenericLong(v);
	}

	@Override
	public Object createFromFloat(float v) {
		return new GenericFloat(v);
	}

	@Override
	public Object createFromDouble(double v) {
		return new GenericDouble(v);
	}

	@Override
	public Object createFromRaw(byte[] b, int offset, int length) {
		return new GenericRaw(b, offset, length);
	}

	@Override
	public Object createFromArray(Object[] obj) {
		// FIXME GenericArray
		return Arrays.asList(obj);
	}

	@Override
	public Object createFromMap(Object[] obj) {
		GenericMap m = new GenericMap(obj.length / 2);
		int i = 0;
		while(i < obj.length) {
			Object k = obj[i++];
			Object v = obj[i++];
			m.put(k, v);
		}
		return m;
	}
	*/
}

