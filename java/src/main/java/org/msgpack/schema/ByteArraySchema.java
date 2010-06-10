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

import java.nio.ByteBuffer;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import org.msgpack.*;

public class ByteArraySchema extends Schema {
	public ByteArraySchema() { }

	@Override
	public String getClassName() {
		return "byte[]";
	}

	@Override
	public String getExpression() {
		return "raw";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException {
		if(obj instanceof byte[]) {
			byte[] b = (byte[])obj;
			pk.packRaw(b.length);
			pk.packRawBody(b);
		} else if(obj instanceof String) {
			try {
				byte[] b = ((String)obj).getBytes("UTF-8");
				pk.packRaw(b.length);
				pk.packRawBody(b);
			} catch (UnsupportedEncodingException e) {
				throw new MessageTypeException();
			}
		} else if(obj == null) {
			pk.packNil();
		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	public static final byte[] convertByteArray(Object obj) throws MessageTypeException {
		if(obj instanceof byte[]) {
			// FIXME copy?
			//byte[] d = (byte[])obj;
			//byte[] v = new byte[d.length];
			//System.arraycopy(d, 0, v, 0, d.length);
			//return v;
			return (byte[])obj;
		} else if(obj instanceof ByteBuffer) {
			ByteBuffer d = (ByteBuffer)obj;
			byte[] v = new byte[d.capacity()];
			int pos = d.position();
			d.get(v);
			d.position(pos);
			return v;
		} else if(obj instanceof String) {
			try {
				return ((String)obj).getBytes("UTF-8");
			} catch (UnsupportedEncodingException e) {
				throw new MessageTypeException();
			}
		} else {
			throw new MessageTypeException();
		}
	}

	@Override
	public Object convert(Object obj) throws MessageTypeException {
		return convertByteArray(obj);
	}

	@Override
	public Object createFromRaw(byte[] b, int offset, int length) {
		byte[] d = new byte[length];
		System.arraycopy(b, offset, d, 0, length);
		return d;
	}
}

