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
package org.msgpack.schema;

import java.util.Collection;
import java.util.List;
import java.lang.reflect.*;
import java.io.IOException;
import org.msgpack.*;

public class SpecificClassSchema extends ClassSchema {
	private Class classCache;
	private Method factoryCache;
	private Constructor constructorCache;

	public SpecificClassSchema(
			String name, String namespace,
			List<String> imports, List<FieldSchema> fields) {
		super(name, namespace, imports, fields);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void pack(Packer pk, Object obj) throws IOException {
		if(obj == null) {
			pk.packNil();
			return;
		}
		if(classCache == null) {
			cacheFactory();
		}
		if(classCache.isInstance(obj)) {
			((MessagePackable)obj).messagePack(pk);
		} else {
			// FIXME Map<String,Object>
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	@Override
	public Object convert(Object obj) throws MessageTypeException {
		if(obj instanceof Collection) {
			if(constructorCache == null) {
				cacheConstructor();
			}
			try {
				MessageMergeable o = (MessageMergeable)constructorCache.newInstance((Object[])null);
				o.messageMerge(obj);
				return o;
			} catch (InvocationTargetException e) {
				throw new RuntimeException("can't instantiate "+fqdn+": "+e.getMessage());
			} catch (InstantiationException e) {
				throw new RuntimeException("can't instantiate "+fqdn+": "+e.getMessage());
			} catch (IllegalAccessException e) {
				throw new RuntimeException("can't instantiate "+fqdn+": "+e.getMessage());
			}

		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	public Schema getElementSchema(int index) {
		// FIXME check index < fields.length
		return fields[index].getSchema();
	}

	public Object createFromArray(Object[] obj) {
		if(factoryCache == null) {
			cacheFactory();
		}
		try {
			return factoryCache.invoke(null, new Object[]{obj});
		} catch (InvocationTargetException e) {
			throw new RuntimeException("can't instantiate "+fqdn+": "+e.getCause());
		} catch (IllegalAccessException e) {
			throw new RuntimeException("can't instantiate "+fqdn+": "+e.getMessage());
		}
	}

	@SuppressWarnings("unchecked")
	private void cacheFactory() {
		try {
			classCache = Class.forName(fqdn);
			factoryCache = classCache.getDeclaredMethod("createFromMessage", new Class[]{Object[].class});
			factoryCache.setAccessible(true);
		} catch(ClassNotFoundException e) {
			throw new RuntimeException("class not found: "+fqdn);
		} catch (NoSuchMethodException e) {
			throw new RuntimeException("class not found: "+fqdn+": "+e.getMessage());
		}
	}

	@SuppressWarnings("unchecked")
	private void cacheConstructor() {
		try {
			classCache = Class.forName(fqdn);
			constructorCache = classCache.getDeclaredConstructor((Class[])null);
			constructorCache.setAccessible(true);
		} catch(ClassNotFoundException e) {
			throw new RuntimeException("class not found: "+fqdn);
		} catch (NoSuchMethodException e) {
			throw new RuntimeException("class not found: "+fqdn+": "+e.getMessage());
		}
	}
}

