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
package org.msgpack.type;

import java.io.IOException;
import org.msgpack.*;
import org.msgpack.template.TemplateRegistry;

public class RawTemplate implements Template {
	static void load() { }

	private RawTemplate() { }

	public void pack(Packer pk, Object target) throws IOException {
		pk.packByteArray(((Raw)target).toByteArray());
	}

	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		return new Raw(pac.unpackByteArray());
	}

	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		return new Raw(from.asByteArray());
	}

	static public RawTemplate getInstance() {
		return instance;
	}

	static final RawTemplate instance = new RawTemplate();

	static {
		TemplateRegistry.register(Raw.class, instance);
	}
}

