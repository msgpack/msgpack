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
package org.msgpack.util.codegen;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

import org.msgpack.MessagePacker;
import org.msgpack.util.codegen.DynamicCodeGenBase.MessagePackerAccessor;

public class DynamicOrdinalEnumPacker {
	public static MessagePacker create(Class<?> c) {
		try {
			DynamicCodeGen gen = DynamicCodeGen.getInstance();
			Class<?> packerClass = gen.generateOrdinalEnumPackerClass(c);
			Constructor<?> cons = packerClass
					.getDeclaredConstructor(new Class[] { Class.class });
			Object obj = cons.newInstance(new Object[] { c });
			((MessagePackerAccessor) obj).setMessagePackers(gen
					.getMessagePackers(c));
			return (MessagePacker) obj;
		} catch (InstantiationException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalAccessException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (SecurityException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (NoSuchMethodException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (IllegalArgumentException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		} catch (InvocationTargetException e) {
			throw new DynamicCodeGenException(e.getMessage(), e);
		}
	}
}
