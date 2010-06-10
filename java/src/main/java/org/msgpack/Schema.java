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

import java.io.Writer;
import java.io.IOException;
import org.msgpack.schema.SSchemaParser;
//import org.msgpack.schema.ClassGenerator;

public abstract class Schema {
	public Schema() { }

	public abstract String getClassName();
	public abstract String getExpression();

	public static Schema parse(String source) {
		return SSchemaParser.parse(source);
	}

	public static Schema load(String source) {
		return SSchemaParser.load(source);
	}

	public abstract void pack(Packer pk, Object obj) throws IOException;
	public abstract Object convert(Object obj) throws MessageTypeException;

	public Object createFromNil() {
		return null;
	}

	public Object createFromBoolean(boolean v) {
		throw new MessageTypeException("type error");
	}

	public Object createFromByte(byte v) {
		throw new MessageTypeException("type error");
	}

	public Object createFromShort(short v) {
		throw new MessageTypeException("type error");
	}

	public Object createFromInt(int v) {
		throw new MessageTypeException("type error");
	}

	public Object createFromLong(long v) {
		throw new MessageTypeException("type error");
	}

	public Object createFromFloat(float v) {
		throw new MessageTypeException("type error");
	}

	public Object createFromDouble(double v) {
		throw new MessageTypeException("type error");
	}

	public Object createFromRaw(byte[] b, int offset, int length) {
		throw new MessageTypeException("type error");
	}
}

