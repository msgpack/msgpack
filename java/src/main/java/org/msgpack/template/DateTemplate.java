//
// MessagePack for Java
//
// Copyright (C) 2009-2011 FURUHASHI Sadayuki
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
package org.msgpack.template;

import java.io.IOException;
import java.util.Date;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

public class DateTemplate implements Template {

	@Override
	public void pack(Packer pk, Object target) throws IOException {
		Date temp = (Date) target;
		pk.packLong(temp.getTime());
	}

	@Override
	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		Long temp = pac.unpackLong();
		return new Date(temp);
	}

	@Override
	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		Long temp = from.asLong();
		return new Date(temp);
	}

	static public DateTemplate getInstance() {
		return instance;
	}

	static final DateTemplate instance = new DateTemplate();

	static {
		TemplateRegistry.register(Date.class, instance);
	}
}
