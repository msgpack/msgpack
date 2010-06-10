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

public class BooleanSchema extends Schema {
	public BooleanSchema() { }

	@Override
	public String getClassName() {
		return "Boolean";
	}

	@Override
	public String getExpression() {
		return "boolean";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException {
		if(obj instanceof Boolean) {
			pk.packBoolean((Boolean)obj);
		} else if(obj == null) {
			pk.packNil();
		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	public static final boolean convertBoolean(Object obj) throws MessageTypeException {
		if(obj instanceof Boolean) {
			return (Boolean)obj;
		}
		throw new MessageTypeException();
	}

	@Override
	public Object convert(Object obj) throws MessageTypeException {
		return convertBoolean(obj);
	}

	@Override
	public Object createFromBoolean(boolean v) {
		return v;
	}
}

