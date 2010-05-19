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
package org.msgpack;

import java.io.IOException;

public class UnpackCursor {
	private Unpacker pac;
	private int offset;

	UnpackCursor(Unpacker pac, int offset)
	{
		this.pac = pac;
		this.offset = offset;
	}

	final void advance(int length) {
		offset += length;
	}

	final int getOffset() {
		return offset;
	}

	public byte unpackByte() throws IOException, MessageTypeException {
		return pac.impl.unpackByte(this, offset);
	}

	public short unpackShort() throws IOException, MessageTypeException {
		return pac.impl.unpackShort(this, offset);
	}

	public int unpackInt() throws IOException, MessageTypeException {
		return pac.impl.unpackInt(this, offset);
	}

	public long unpackLong() throws IOException, MessageTypeException {
		return pac.impl.unpackLong(this, offset);
	}

	public float unpackFloat() throws IOException, MessageTypeException {
		return pac.impl.unpackFloat(this, offset);
	}

	public double unpackDouble() throws IOException, MessageTypeException {
		return pac.impl.unpackDouble(this, offset);
	}

	public Object unpackNull() throws IOException, MessageTypeException {
		return pac.impl.unpackNull(this, offset);
	}

	public boolean unpackBoolean() throws IOException, MessageTypeException {
		return pac.impl.unpackBoolean(this, offset);
	}

	public int unpackArray() throws IOException, MessageTypeException {
		return pac.impl.unpackArray(this, offset);
	}

	public int unpackMap() throws IOException, MessageTypeException {
		return pac.impl.unpackMap(this, offset);
	}

	public int unpackRaw() throws IOException, MessageTypeException {
		return pac.impl.unpackRaw(this, offset);
	}

	public byte[] unpackRawBody(int length) throws IOException, MessageTypeException {
		return pac.impl.unpackRawBody(this, offset, length);
	}

	public String unpackString() throws IOException, MessageTypeException {
		return pac.impl.unpackString(this, offset);
	}

	public void commit() {
		pac.setOffset(offset);
	}
}

