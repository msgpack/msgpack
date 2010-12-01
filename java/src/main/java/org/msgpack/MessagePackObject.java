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

import java.util.List;
import java.util.Set;
import java.util.Map;
import java.math.BigInteger;
import org.msgpack.template.TemplateRegistry;

public abstract class MessagePackObject implements Cloneable, MessagePackable {
	public boolean isNil() {
		return false;
	}

	public boolean isBooleanType() {
		return false;
	}

	public boolean isIntegerType() {
		return false;
	}

	public boolean isFloatType() {
		return false;
	}

	public boolean isArrayType() {
		return false;
	}

	public boolean isMapType() {
		return false;
	}

	public boolean isRawType() {
		return false;
	}

	public boolean asBoolean() {
		throw new MessageTypeException("type error");
	}

	public byte asByte() {
		throw new MessageTypeException("type error");
	}

	public short asShort() {
		throw new MessageTypeException("type error");
	}

	public int asInt() {
		throw new MessageTypeException("type error");
	}

	public long asLong() {
		throw new MessageTypeException("type error");
	}

	public BigInteger asBigInteger() {
		throw new MessageTypeException("type error");
	}

	public float asFloat() {
		throw new MessageTypeException("type error");
	}

	public double asDouble() {
		throw new MessageTypeException("type error");
	}

	public byte[] asByteArray() {
		throw new MessageTypeException("type error");
	}

	public String asString() {
		throw new MessageTypeException("type error");
	}

	public MessagePackObject[] asArray() {
		throw new MessageTypeException("type error");
	}

	public List<MessagePackObject> asList() {
		throw new MessageTypeException("type error");
	}

	public Map<MessagePackObject, MessagePackObject> asMap() {
		throw new MessageTypeException("type error");
	}

	public byte byteValue() {
		throw new MessageTypeException("type error");
	}

	public short shortValue() {
		throw new MessageTypeException("type error");
	}

	public int intValue() {
		throw new MessageTypeException("type error");
	}

	public long longValue() {
		throw new MessageTypeException("type error");
	}

	public BigInteger bigIntegerValue() {
		throw new MessageTypeException("type error");
	}

	public float floatValue() {
		throw new MessageTypeException("type error");
	}

	public double doubleValue() {
		throw new MessageTypeException("type error");
	}

	abstract public Object clone();

	public Object convert(Template tmpl) throws MessageTypeException {
		return convert(tmpl, null);
	}

	public <T> T convert(Template tmpl, T to) throws MessageTypeException {
		return (T)tmpl.convert(this, to);
	}

	public <T> T convert(Class<T> klass) throws MessageTypeException {
		return convert(klass, null);
	}

	public <T> T convert(T to) throws MessageTypeException {
		return convert((Class<T>)to.getClass(), to);
	}

	public <T> T convert(Class<T> klass, T to) throws MessageTypeException {
		if(isNil()) {
			return null;
		}
		return (T)convert(TemplateRegistry.lookup(klass), to);
	}
}

