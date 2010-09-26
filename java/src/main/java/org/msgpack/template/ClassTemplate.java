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

public class ClassTemplate implements Template {
	private Class klass;

	public ClassTemplate(Class klass) {
		this.klass = klass;
	}

	public Object unpack(Unpacker pac) throws IOException, MessageTypeException {
		try {
			return pac.unpack(klass);
		} catch (IllegalAccessException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		} catch (InstantiationException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		}
	}

	public Object convert(MessagePackObject from) throws MessageTypeException {
		if(MessageConvertable.class.isAssignableFrom(klass)) {
			Object obj;
			try {
				obj = klass.newInstance();
			} catch (IllegalAccessException e) {
				throw new MessageTypeException(e.getMessage());  // FIXME
			} catch (InstantiationException e) {
				throw new MessageTypeException(e.getMessage());  // FIXME
			}
			((MessageConvertable)obj).messageConvert(from);
			return obj;
		}

		MessageConverter converter = CustomConverter.get(klass);
		if(converter != null) {
			return converter.convert(from);
		}

		// FIXME check annotations -> code generation -> CustomMessage.registerTemplate

		throw new MessageTypeException();
	}
}

