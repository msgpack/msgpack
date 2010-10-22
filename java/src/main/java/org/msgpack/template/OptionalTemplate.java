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

import java.io.IOException;
import org.msgpack.*;

public class OptionalTemplate implements Template {
	private Template elementTemplate;
	private Object defaultObject;

	public OptionalTemplate(Template elementTemplate) {
		this(elementTemplate, null);
	}

	public OptionalTemplate(Template elementTemplate, Object defaultObject) {
		this.elementTemplate = elementTemplate;
		this.defaultObject = defaultObject;
	}

	public Object unpack(Unpacker pac) throws IOException, MessageTypeException {
		if(pac.tryUnpackNull()) {
			return defaultObject;
		}
		return elementTemplate.unpack(pac);
	}

	public Object convert(MessagePackObject from) throws MessageTypeException {
		if(from.isNil()) {
			return defaultObject;
		}
		return elementTemplate.convert(from);
	}
}

