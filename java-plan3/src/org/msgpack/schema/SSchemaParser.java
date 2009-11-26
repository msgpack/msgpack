//
// MessagePack for Java
//
// Copyright (C) 2009 FURUHASHI Sadayuki
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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Stack;
import java.util.regex.Pattern;
import java.util.regex.Matcher;
import org.msgpack.*;

// FIXME exception class

public class SSchemaParser {
	public static Schema parse(String source) {
		return new SSchemaParser(false).run(source);
	}

	public static Schema load(String source) {
		return new SSchemaParser(true).run(source);
	}

	private static abstract class SExp {
		boolean isAtom() { return false; }
		public String getAtom() { return null; }

		boolean isTuple() { return false; }
		public SExp getTuple(int i) { return null; }
		public int size() { return 0; }
		public boolean empty() { return size() == 0; }
		Iterator<SExp> iterator(int offset) { return null; }
	}

	private static class SAtom extends SExp {
		private String atom;

		SAtom(String atom) { this.atom = atom; }

		boolean isAtom() { return true; }
		public String getAtom() { return atom; }

		public String toString() { return atom; }
	}

	private static class STuple extends SExp {
		private List<SExp> tuple;

		STuple() { this.tuple = new ArrayList<SExp>(); }

		public void add(SExp e) { tuple.add(e); }

		boolean isTuple() { return true; }
		public SExp getTuple(int i) { return tuple.get(i); }
		public int size() { return tuple.size(); }

		Iterator<SExp> iterator(int skip) {
			Iterator<SExp> i = tuple.iterator();
			for(int s=0; s < skip; ++s) { i.next(); }
			return i;
		}

		public String toString() {
			if(tuple.isEmpty()) { return "()"; }
			Iterator<SExp> i = tuple.iterator();
			StringBuffer o = new StringBuffer();
			o.append("(").append(i.next());
			while(i.hasNext()) { o.append(" ").append(i.next()); }
			o.append(")");
			return o.toString();
		}
	}

	boolean specificClass;

	private SSchemaParser(boolean specificClass) {
		this.specificClass = specificClass;
	}

	private static Pattern pattern = Pattern.compile(
			"(?:\\s+)|([\\(\\)]|[\\d\\w\\.]+)");

	private Schema run(String source) {
		Matcher m = pattern.matcher(source);

		Stack<STuple> stack = new Stack<STuple>();
		String token;

		while(true) {
			while(true) {
				if(!m.find()) { throw new RuntimeException("unexpected end of file"); }
				token = m.group(1);
				if(token != null) { break; }
			}

			if(token.equals("(")) {
				stack.push(new STuple());
			} else if(token.equals(")")) {
				STuple top = stack.pop();
				if(stack.empty()) {
					stack.push(top);
					break;
				}
				stack.peek().add(top);
			} else {
				if(stack.empty()) {
					throw new RuntimeException("unexpected token '"+token+"'");
				}
				stack.peek().add(new SAtom(token));
			}
		}

		while(true) {
			if(!m.find()) { break; }
			token = m.group(1);
			if(token != null) { throw new RuntimeException("unexpected token '"+token+"'"); }
		}

		return readType( stack.pop() );
	}

	private Schema readType(SExp exp) {
		if(exp.isAtom()) {
			String type = exp.getAtom();
			if(type.equals("string")) {
				return new StringSchema();
			} else if(type.equals("raw")) {
				return new RawSchema();
			} else if(type.equals("byte")) {
				return new ByteSchema();
			} else if(type.equals("short")) {
				return new ShortSchema();
			} else if(type.equals("int")) {
				return new IntSchema();
			} else if(type.equals("long")) {
				return new LongSchema();
			} else if(type.equals("float")) {
				return new FloatSchema();
			} else if(type.equals("double")) {
				return new DoubleSchema();
			} else if(type.equals("object")) {
				return new GenericSchema();
			} else {
				throw new RuntimeException("byte, short, int, long, float, double, raw, string or object is expected but got '"+type+"': "+exp);
			}
		} else {
			String type = exp.getTuple(0).getAtom();
			if(type.equals("class")) {
				return parseClass(exp);
			} else if(type.equals("array")) {
				return parseArray(exp);
			} else if(type.equals("map")) {
				return parseMap(exp);
			} else {
				throw new RuntimeException("class, array or map is expected but got '"+type+"': "+exp);
			}
		}
	}

	private ClassSchema parseClass(SExp exp) {
		if(exp.size() < 3 || !exp.getTuple(1).isAtom()) {
			throw new RuntimeException("class is (class NAME CLASS_BODY): "+exp);
		}

		String namespace = null;
		List<String> imports = new ArrayList<String>();
		String name = exp.getTuple(1).getAtom();
		List<FieldSchema> fields = new ArrayList<FieldSchema>();

		for(Iterator<SExp> i=exp.iterator(2); i.hasNext();) {
			SExp subexp = i.next();
			if(!subexp.isTuple() || subexp.empty() || !subexp.getTuple(0).isAtom()) {
				throw new RuntimeException("field, package or import is expected: "+subexp);
			}
			String type = subexp.getTuple(0).getAtom();
			if(type.equals("field")) {
				fields.add( parseField(subexp) );
			} else if(type.equals("package")) {
				if(namespace != null) {
					throw new RuntimeException("duplicated package definition: "+subexp);
				}
				namespace = parseNamespace(subexp);
			} else if(type.equals("import")) {
				imports.add( parseImport(subexp) );
			} else {
				throw new RuntimeException("field, package or import is expected but got '"+type+"': "+subexp);
			}
		}

		if(specificClass) {
			return new SpecificClassSchema(name, namespace, imports, fields);
		} else {
			return new GenericClassSchema(name, namespace, imports, fields);
		}
	}

	private ArraySchema parseArray(SExp exp) {
		if(exp.size() != 2) {
			throw new RuntimeException("array is (array ELEMENT_TYPE): "+exp);
		}
		Schema elementType = readType(exp.getTuple(1));
		return new ArraySchema(elementType);
	}

	private MapSchema parseMap(SExp exp) {
		if(exp.size() != 3 || !exp.getTuple(1).isAtom()) {
			throw new RuntimeException("map is (map KEY_TYPE VALUE_TYPE): "+exp);
		}
		Schema keyType   = readType(exp.getTuple(1));
		Schema valueType = readType(exp.getTuple(2));
		return new MapSchema(keyType, valueType);
	}

	private String parseNamespace(SExp exp) {
		if(exp.size() != 2 || !exp.getTuple(1).isAtom()) {
			throw new RuntimeException("package is (package NAME): "+exp);
		}
		String name = exp.getTuple(1).getAtom();
		return name;
	}

	private String parseImport(SExp exp) {
		if(exp.size() != 2 || !exp.getTuple(1).isAtom()) {
			throw new RuntimeException("import is (import NAME): "+exp);
		}
		String name = exp.getTuple(1).getAtom();
		return name;
	}

	private FieldSchema parseField(SExp exp) {
		if(exp.size() != 3 || !exp.getTuple(1).isAtom()) {
			throw new RuntimeException("field is (field NAME TYPE): "+exp);
		}
		String name = exp.getTuple(1).getAtom();
		Schema type = readType(exp.getTuple(2));
		return new FieldSchema(name, type);
	}
}

