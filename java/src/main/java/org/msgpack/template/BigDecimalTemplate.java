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
import java.math.BigDecimal;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

public class BigDecimalTemplate implements Template {

	@Override
	public void pack(Packer pk, Object target) throws IOException {
		BigDecimal temp = (BigDecimal) target;
		try {
			pk.packString(temp.toString());
		} catch (NullPointerException e) {
			throw new MessageTypeException("target is null.", e);
		}
	}

	@Override
	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		String temp = pac.unpackString();
		return new BigDecimal(temp);
	}

	@Override
	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		String temp = from.asString();
		return new BigDecimal(temp);
	}

	static public BigDecimalTemplate getInstance() {
		return instance;
	}

	static final BigDecimalTemplate instance = new BigDecimalTemplate();

	static {
		TemplateRegistry.register(BigDecimal.class, instance);
	}
}
