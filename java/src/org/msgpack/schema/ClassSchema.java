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
import java.util.List;
import org.msgpack.*;

public abstract class ClassSchema extends Schema implements IArraySchema {
	protected FieldSchema[] fields;
	protected List<String> imports;
	protected String namespace;
	protected String fqdn;

	public ClassSchema(
			String name, String namespace,
			List<String> imports, List<FieldSchema> fields) {
		super(name);
		this.namespace = namespace;
		this.imports = imports;  // FIXME clone?
		this.fields = new FieldSchema[fields.size()];
		System.arraycopy(fields.toArray(), 0, this.fields, 0, fields.size());
		if(namespace == null) {
			this.fqdn = name;
		} else {
			this.fqdn = namespace+"."+name;
		}
	}

	public final FieldSchema[] getFields() {
		return fields;
	}

	String getNamespace() {
		return namespace;
	}

	List<String> getImports() {
		return imports;
	}

	void setNamespace(String namespace) {
		this.namespace = namespace;
	}

	void setImports(List<String> imports) {
		this.imports = imports;  // FIXME clone?
	}

	//@Override
	//public String getFullName()
	//{
	//	if(namespace == null) {
	//		return getName();
	//	} else {
	//		return namespace+"."+getName();
	//	}
	//}

	@Override
	public String getExpression() {
		StringBuffer b = new StringBuffer();
		b.append("(class ");
		b.append(getName());
		if(namespace != null) {
			b.append(" (package "+namespace+")");
		}
		for(FieldSchema f : fields) {
			b.append(" "+f.getExpression());
		}
		b.append(")");
		return b.toString();
	}

	public boolean equals(SpecificClassSchema o) {
		return (namespace != null ? namespace.equals(o.getNamespace()) : o.getNamespace() == null) &&
			getName().equals(o.getName());
	}
}

