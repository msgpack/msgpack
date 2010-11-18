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

import java.io.OutputStream;
import java.io.InputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import org.msgpack.util.codegen.DynamicTemplate;
import org.msgpack.util.codegen.DynamicOrdinalEnumTemplate;
import org.msgpack.util.codegen.FieldList;

public class MessagePack {
	public static byte[] pack(Object obj) {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		try {
			new Packer(out).pack(obj);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		return out.toByteArray();
	}

	public static void pack(OutputStream out, Object obj) throws IOException {
		new Packer(out).pack(obj);
	}

	public static byte[] pack(Object obj, Template tmpl) throws MessageTypeException {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		try {
			new Packer(out).pack(obj, tmpl);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		return out.toByteArray();
	}

	public static void pack(OutputStream out, Object obj, Template tmpl) throws IOException, MessageTypeException {
		new Packer(out).pack(obj, tmpl);
	}


	public static MessagePackObject unpack(byte[] buffer) throws MessageTypeException {
		Unpacker pac = new Unpacker();
		pac.wrap(buffer);
		try {
			return pac.unpackObject();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static Object unpack(byte[] buffer, Template tmpl) throws MessageTypeException {
		Unpacker pac = new Unpacker();
		pac.wrap(buffer);
		try {
			return pac.unpack(tmpl);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static <T> T unpack(byte[] buffer, Template tmpl, T to) throws MessageTypeException {
		Unpacker pac = new Unpacker();
		pac.wrap(buffer);
		try {
			return pac.unpack(tmpl, to);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static <T> T unpack(byte[] buffer, Class<T> klass) throws MessageTypeException {
		Unpacker pac = new Unpacker();
		pac.wrap(buffer);
		try {
			return pac.unpack(klass);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static <T> T unpack(byte[] buffer, T to) throws MessageTypeException {
		Unpacker pac = new Unpacker();
		pac.wrap(buffer);
		try {
			return pac.unpack(to);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static MessagePackObject unpack(InputStream in) throws IOException {
		Unpacker pac = new Unpacker(in);
		return pac.unpackObject();
	}

	public static Object unpack(InputStream in, Template tmpl) throws IOException, MessageTypeException {
		Unpacker pac = new Unpacker(in);
		try {
			return pac.unpack(tmpl);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static <T> T unpack(InputStream in, Template tmpl, T to) throws IOException, MessageTypeException {
		Unpacker pac = new Unpacker(in);
		try {
			return pac.unpack(tmpl, to);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static <T> T unpack(InputStream in, Class<T> klass) throws IOException, MessageTypeException {
		Unpacker pac = new Unpacker(in);
		try {
			return pac.unpack(klass);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static <T> T unpack(InputStream in, T to) throws IOException, MessageTypeException {
		Unpacker pac = new Unpacker(in);
		try {
			return pac.unpack(to);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static void register(Class<?> target) {  // auto-detect
		Template tmpl;
		if(target.isEnum()) {
			tmpl = DynamicOrdinalEnumTemplate.create(target);
		//} else if(List.isAssignableFrom(target)) {
		//} else if(Set.isAssignableFrom(target)) {
		//} else if(Map.isAssignableFrom(target)) {
		//} else if(Collection.isAssignableFrom(target)) {
		//} else if(BigInteger.isAssignableFrom(target)) {
		} else {
			if (MessagePackTemplateProvider.class.isAssignableFrom(target)) {
				try {
					tmpl = ((MessagePackTemplateProvider) target.newInstance()).getTemplate();
				} catch (InstantiationException e) {
					throw new RuntimeException(e);
				} catch (IllegalAccessException e) {
					throw new RuntimeException(e);
				}
			} else {
				tmpl = DynamicTemplate.create(target);
			}
		}

		CustomPacker.register(target, tmpl);
		CustomConverter.register(target, tmpl);
		CustomUnpacker.register(target, tmpl);
	}

	public static void register(Class<?> target, FieldList opts) {
		Template tmpl = DynamicTemplate.create(target, opts);
		CustomPacker.register(target, tmpl);
		CustomConverter.register(target, tmpl);
		CustomUnpacker.register(target, tmpl);
	}

	public static void register(Class<?> target, Template tmpl) {
		CustomPacker.register(target, tmpl);
		CustomConverter.register(target, tmpl);
		CustomUnpacker.register(target, tmpl);
	}

	public static void registerPacker(Class<?> target, MessagePacker packer) {
		CustomPacker.register(target, packer);
	}

	public static void registerConverter(Class<?> target, MessageConverter converter) {
		CustomConverter.register(target, converter);
	}

	public static void registerUnpacker(Class<?> target, MessageUnpacker unpacker) {
		CustomUnpacker.register(target, unpacker);
	}
}

