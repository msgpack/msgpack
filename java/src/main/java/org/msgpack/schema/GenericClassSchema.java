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
import java.util.Map;
import java.util.HashMap;
import java.io.IOException;
import org.msgpack.*;

public class GenericClassSchema extends ClassSchema {
	public GenericClassSchema(
			String name, String namespace,
			List<String> imports, List<FieldSchema> fields) {
		super(name, namespace, imports, fields);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void pack(Packer pk, Object obj) throws IOException {
		if(obj instanceof Map) {
			Map d = (Map)obj;
			pk.packArray(fields.length);
			for(int i=0; i < fields.length; ++i) {
				FieldSchema f = fields[i];
				f.getSchema().pack(pk, d.get(f.getName()));
			}
		} else if(obj == null) {
			pk.packNil();
		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	@Override
	public Object convert(Object obj) throws MessageTypeException {
		if(obj instanceof Collection) {
			// FIXME optimize
			return createFromArray( ((Collection)obj).toArray() );
		} else if(obj instanceof Map) {
			HashMap<String,Object> m = new HashMap<String,Object>(fields.length);
			Map d = (Map)obj;
			for(int i=0; i < fields.length; ++i) {
				FieldSchema f = fields[i];
				String fieldName = f.getName();
				m.put(fieldName, f.getSchema().convert(d.get(fieldName)));
			}
			return m;
		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	public Schema getElementSchema(int index) {
		// FIXME check index < fields.length
		return fields[index].getSchema();
	}

	public Object createFromArray(Object[] obj) {
		HashMap<String,Object> m = new HashMap<String,Object>(fields.length);
		int i=0;
		for(; i < obj.length; ++i) {
			m.put(fields[i].getName(), obj[i]);
		}
		for(; i < fields.length; ++i) {
			m.put(fields[i].getName(), null);
		}
		return m;
	}
}

