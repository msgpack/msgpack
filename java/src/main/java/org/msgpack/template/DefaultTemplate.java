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
import java.lang.reflect.Type;
import org.msgpack.*;

public class DefaultTemplate implements Template {
	private Class<?> targetClass;
	private Type lookupType;
	private boolean messagePackable;
	private boolean messageUnpackable;
	private boolean messageConvertable;

	public DefaultTemplate(Class<?> targetClass) {
		this(targetClass, (Type)targetClass);
	}

	public DefaultTemplate(Class<?> targetClass, Type lookupType) {
		this.targetClass = targetClass;
		this.lookupType = lookupType;
		this.messagePackable = MessagePackable.class.isAssignableFrom(targetClass);
		this.messageUnpackable = MessageUnpackable.class.isAssignableFrom(targetClass);
		this.messageConvertable = MessageConvertable.class.isAssignableFrom(targetClass);
	}

	public void pack(Packer pk, Object target) throws IOException {
		if(messagePackable) {
			((MessagePackable)target).messagePack(pk);
			return;
		}
		Template tmpl = TemplateRegistry.tryLookup(lookupType);
		if(tmpl == this || tmpl == null) {
			throw new MessageTypeException();
		}
		tmpl.pack(pk, target);
	}

	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		if(messageUnpackable) {
			if(to == null) {
				try {
					to = targetClass.newInstance();
				} catch (Exception e) {
					throw new MessageTypeException(e);
				}
			}
			((MessageUnpackable)to).messageUnpack(pac);
			return to;
		}
		Template tmpl = TemplateRegistry.tryLookup(lookupType);
		if(tmpl == this || tmpl == null) {
			throw new MessageTypeException();
		}
		return tmpl.unpack(pac, to);
	}

	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		if(messageConvertable) {
			if(to == null) {
				try {
					to = targetClass.newInstance();
				} catch (Exception e) {
					throw new MessageTypeException(e);
				}
			}
			((MessageConvertable)to).messageConvert(from);
			return from;
		}
		Template tmpl = TemplateRegistry.tryLookup(lookupType);
		if(tmpl == this || tmpl == null) {
			throw new MessageTypeException();
		}
		return tmpl.convert(from, to);
	}
}

