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
import java.util.RandomAccess;
import java.io.IOException;
import org.msgpack.*;

public class ArraySchema extends Schema implements IArraySchema {
	private Schema elementSchema;

	public ArraySchema(Schema elementSchema)
	{
		super("array");
		this.elementSchema = elementSchema;
	}

	@Override
	public String getFullName()
	{
		return "List<"+elementSchema.getFullName()+">";
	}

	@Override
	public String getExpression()
	{
		return "(array "+elementSchema.getExpression()+")";
	}

	@Override
	@SuppressWarnings("unchecked")
	public void pack(Packer pk, Object obj) throws IOException
	{
		if(obj instanceof List) {
			ArrayList<Object> d = (ArrayList<Object>)obj;
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

	@Override
	@SuppressWarnings("unchecked")
	public Object convert(Object obj) throws MessageTypeException
	{
		if(obj instanceof List) {
			List d = (List)obj;
			ArrayList ar = new ArrayList(d.size());
			if(obj instanceof RandomAccess) {
				for(int i=0; i < d.size(); ++i) {
					ar.add( elementSchema.convert(d.get(i)) );
				}
			} else {
				for(Object e : d) {
					ar.add( elementSchema.convert(e) );
				}
			}
			return ar;

		} else if(obj instanceof Collection) {
			Collection d = (Collection)obj;
			ArrayList ar = new ArrayList(d.size());
			for(Object e : (Collection)obj) {
				ar.add( elementSchema.convert(e) );
			}
			return ar;

		} else {
			throw MessageTypeException.invalidConvert(obj, this);
		}
	}

	@Override
	public Schema getElementSchema(int index)
	{
		return elementSchema;
	}

	@Override
	public Object createFromArray(Object[] obj)
	{
		return Arrays.asList(obj);
	}
}

