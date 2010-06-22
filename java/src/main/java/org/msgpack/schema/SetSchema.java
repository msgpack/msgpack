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

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.RandomAccess;
import java.io.IOException;
import org.msgpack.*;

public class SetSchema extends Schema implements IArraySchema {
	private Schema elementSchema;

	public SetSchema(Schema elementSchema) {
		this.elementSchema = elementSchema;
	}

	@Override
	public String getClassName() {
		return "Set<"+elementSchema.getClassName()+">";
	}

	@Override
	public String getExpression() {
		return "(set "+elementSchema.getExpression()+")";
	}

	@Override
	public void pack(Packer pk, Object obj) throws IOException {
		if(obj instanceof List) {
			List<Object> d = (List<Object>)obj;
			pk.packArray(d.size());
			if(obj instanceof RandomAccess) {
				for(int i=0; i < d.size(); ++i) {
					elementSchema.pack(pk, d.get(i));
				}
			} else {
				for(Object e : d) {
					elementSchema.pack(pk, e);
				}
			}
		} else if(obj instanceof Set) {
			Set<Object> d = (Set<Object>)obj;
			pk.packArray(d.size());
			for(Object e : d) {
				elementSchema.pack(pk, e);
			}
		} else if(obj == null) {
			pk.packNil();
		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	@SuppressWarnings("unchecked")
	public static final <T> Set<T> convertSet(Object obj,
			Schema elementSchema, Set<T> dest) throws MessageTypeException {
		if(!(obj instanceof List)) {
			throw new MessageTypeException();
		}
		List<Object> d = (List<Object>)obj;
		if(dest == null) {
			dest = new HashSet<T>(d.size());
		}
		if(obj instanceof RandomAccess) {
			for(int i=0; i < d.size(); ++i) {
				dest.add( (T)elementSchema.convert(d.get(i)) );
			}
		} else {
			for(Object e : d) {
				dest.add( (T)elementSchema.convert(e) );
			}
		}
		return dest;
	}

	@Override
	public Object convert(Object obj) throws MessageTypeException {
		return convertSet(obj, elementSchema, null);
	}

	@Override
	public Schema getElementSchema(int index) {
		return elementSchema;
	}

	@Override
	public Object createFromArray(Object[] obj) {
		Set m = new HashSet(obj.length);
		for(int i=0; i < obj.length; i++) {
			m.add(obj[i]);
		}
		return m;
	}
}

