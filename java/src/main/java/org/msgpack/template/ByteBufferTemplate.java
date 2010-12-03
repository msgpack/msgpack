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
package org.msgpack.template;

import java.nio.ByteBuffer;
import java.io.IOException;
import org.msgpack.*;

public class ByteBufferTemplate implements Template {
	private ByteBufferTemplate() {
	}

	public void pack(Packer pk, Object target) throws IOException {
		pk.pack((ByteBuffer) target);
	}

	public Object unpack(Unpacker pac, Object to) throws IOException,
			MessageTypeException {
		return pac.unpackByteBuffer();
	}

	public Object convert(MessagePackObject from, Object to)
			throws MessageTypeException {
		// FIXME
		byte[] bytes = from.asByteArray();
		return ByteBuffer.wrap(bytes);
	}

	static public ByteBufferTemplate getInstance() {
		return instance;
	}

	static final ByteBufferTemplate instance = new ByteBufferTemplate();

	static {
		TemplateRegistry.register(ByteBuffer.class, instance);
	}
}
