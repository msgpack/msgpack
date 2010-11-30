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
import org.msgpack.annotation.MessagePackDelegate;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.msgpack.util.codegen.DynamicTemplate;
import org.msgpack.util.codegen.DynamicOrdinalEnumTemplate;

import java.util.*;
import java.math.BigInteger;
import java.nio.ByteBuffer;

public class ClassTemplate implements Template {
	static {
		Templates.load();
	}

	private Class<?> klass;

	public ClassTemplate(Class<?> klass) {
		this.klass = klass;
	}

	public void pack(Packer pk, Object o) throws IOException {
		// FIXME
		if(o == null) {
			pk.packNil();
			return;
		}
		//if(o instanceof String) {
		//	pk.packString((String)o);
		//	return;
		//}
		if(o instanceof MessagePackable) {
			((MessagePackable)o).messagePack(pk);
			return;
		}
		//if(o instanceof byte[]) {
		//	pk.packByteArray((byte[])o);
		//	return;
		//}
		if(o instanceof List) {
			List<Object> l = (List<Object>)o;
			pk.packArray(l.size());
			for(Object i : l) {
				pk.pack(i);
			}
			return;
		}
		if(o instanceof Set) {
			Set<Object> l = (Set<Object>)o;
			pk.packArray(l.size());
			for(Object i : l) {
				pk.pack(i);
			}
			return;
		}
		if(o instanceof Map) {
			Map<Object,Object> m = (Map<Object,Object>)o;
			pk.packMap(m.size());
			for(Map.Entry<Object,Object> e : m.entrySet()) {
				pk.pack(e.getKey());
				pk.pack(e.getValue());
			}
			return;
		}
		if(o instanceof Collection) {
			Collection<Object> l = (Collection<Object>)o;
			pk.packArray(l.size());
			for(Object i : l) {
				pk.pack(i);
			}
			return;
		}
		//if(o instanceof Boolean) {
		//	pk.packBoolean((Boolean)o);
		//	return;
		//}
		//if(o instanceof Integer) {
		//	pk.packInt((Integer)o);
		//	return;
		//}
		//if(o instanceof Long) {
		//	pk.packLong((Long)o);
		//	return;
		//}
		//if(o instanceof Short) {
		//	pk.packShort((Short)o);
		//	return;
		//}
		//if(o instanceof Byte) {
		//	pk.packByte((Byte)o);
		//	return;
		//}
		//if(o instanceof Float) {
		//	pk.packFloat((Float)o);
		//	return;
		//}
		//if(o instanceof Double) {
		//	pk.packDouble((Double)o);
		//	return;
		//}
		if(o instanceof BigInteger) {
			pk.packBigInteger((BigInteger)o);
			return;
		}
		if (o instanceof ByteBuffer) { // FIXME
			Templates.tByteBuffer().pack(pk, o);
			return;
		}

		MessagePacker packer = CustomPacker.get(klass);
		if(packer != null) {
			packer.pack(pk, o);
			return;
		}

		if (CustomMessage.isAnnotated(klass, MessagePackMessage.class)) {
			Template tmpl = DynamicTemplate.create(klass);
			CustomMessage.register(klass, tmpl);
			tmpl.pack(pk, o);
			return;
		} else if (CustomMessage.isAnnotated(klass, MessagePackDelegate.class)) {
			// FIXME DelegatePacker
			throw new UnsupportedOperationException("not supported yet. : " + klass.getName());
		} else if (CustomMessage.isAnnotated(klass, MessagePackOrdinalEnum.class)) {
			Template tmpl = DynamicOrdinalEnumTemplate.create(klass);
			CustomMessage.register(klass, tmpl);
			tmpl.pack(pk, o);
			return;
		}

		throw new MessageTypeException("unknown object "+o+" ("+o.getClass()+")");
	}

	@Override
	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		try {
			MessageUnpacker unpacker = CustomUnpacker.get(klass);
			if(unpacker != null) {
				return unpacker.unpack(pac, to);
			}

			if(MessageUnpackable.class.isAssignableFrom(klass)) {
				MessageUnpackable obj;
				if(to == null) {
					obj = (MessageUnpackable)klass.newInstance();
				} else {
					obj = (MessageUnpackable)to;
				}
				obj.messageUnpack(pac);
				return obj;
			}

			if (CustomMessage.isAnnotated(klass, MessagePackMessage.class)) {
				Template tmpl = DynamicTemplate.create(klass);
				CustomMessage.register(klass, tmpl);
				return tmpl.unpack(pac, to);
			} else if (CustomMessage.isAnnotated(klass, MessagePackDelegate.class)) {
				// TODO DelegateUnpacker
				throw new UnsupportedOperationException("not supported yet. : " + klass.getName());
			} else if (CustomMessage.isAnnotated(klass, MessagePackOrdinalEnum.class)) {
				Template tmpl = DynamicOrdinalEnumTemplate.create(klass);
				CustomMessage.register(klass, tmpl);
				return tmpl.unpack(pac, to);
			}

			// fallback
			MessageConverter converter = null;

			if (CustomMessage.isAnnotated(klass, MessagePackMessage.class)) {
				Template tmpl = DynamicTemplate.create(klass);
				CustomMessage.register(klass, tmpl);
				return tmpl.convert(pac.unpackObject(), to);
			} else if (CustomMessage.isAnnotated(klass, MessagePackDelegate.class)) {
				// TODO DelegateConverter
				throw new UnsupportedOperationException("not supported yet. : " + klass.getName());
			} else if (CustomMessage.isAnnotated(klass, MessagePackOrdinalEnum.class)) {
				Template tmpl = DynamicOrdinalEnumTemplate.create(klass);
				CustomMessage.register(klass, tmpl);
				return tmpl.convert(pac.unpackObject(), to);
			}

			throw new MessageTypeException("unknown type: "+klass);

		} catch (IllegalAccessException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		} catch (InstantiationException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		}
	}

	@Override
	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		try {
			MessageConverter converter = CustomConverter.get(klass);
			if(converter != null) {
				return converter.convert(from, to);
			}

			if(MessageConvertable.class.isAssignableFrom(klass)) {
				MessageConvertable obj;
				if(to == null) {
					obj = (MessageConvertable)klass.newInstance();
				} else {
					obj = (MessageConvertable)to;
				}
				obj.messageConvert(from);
				return obj;
			}

			if (CustomMessage.isAnnotated(klass, MessagePackMessage.class)) {
				Template tmpl = DynamicTemplate.create(klass);
				CustomMessage.register(klass, tmpl);
				return tmpl.convert(from, to);
			} else if (CustomMessage.isAnnotated(klass, MessagePackDelegate.class)) {
				// TODO DelegateConverter
				throw new UnsupportedOperationException("not supported yet. : " + klass.getName());
			} else if (CustomMessage.isAnnotated(klass, MessagePackOrdinalEnum.class)) {
				Template tmpl = DynamicOrdinalEnumTemplate.create(klass);
				CustomMessage.register(klass, tmpl);
				return tmpl.convert(from, to);
			}

			throw new MessageTypeException();

		} catch (IllegalAccessException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		} catch (InstantiationException e) {
			throw new MessageTypeException(e.getMessage());  // FIXME
		}
	}
}

