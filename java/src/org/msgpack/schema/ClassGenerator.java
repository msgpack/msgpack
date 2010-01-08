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

import java.util.ArrayList;
import java.util.List;
import java.io.IOException;
import java.io.File;
import java.io.Writer;
import org.msgpack.*;

public class ClassGenerator {
	private ClassSchema schema;
	private Writer writer;
	private int indent;

	private ClassGenerator(Writer writer) {
		this.writer = writer;
		this.indent = 0;
	}

	public static void write(Schema schema, Writer dest) throws IOException {
		if(!(schema instanceof ClassSchema)) {
			throw new RuntimeException("schema is not class schema");
		}
		ClassSchema cs = (ClassSchema)schema;
		new ClassGenerator(dest).run(cs);
	}

	private void run(ClassSchema cs) throws IOException {
		List<ClassSchema> subclasses = new ArrayList<ClassSchema>();
		for(FieldSchema f : cs.getFields()) {
			findSubclassSchema(subclasses, f.getSchema());
		}

		for(ClassSchema sub : subclasses) {
			sub.setNamespace(cs.getNamespace());
			sub.setImports(cs.getImports());
		}

		this.schema = cs;

		writeHeader();

		writeClass();

		for(ClassSchema sub : subclasses) {
			this.schema = sub;
			writeSubclass();
		}

		writeFooter();

		this.schema = null;
		writer.flush();
	}

	private void findSubclassSchema(List<ClassSchema> dst, Schema s) {
		if(s instanceof ClassSchema) {
			ClassSchema cs = (ClassSchema)s;
			if(!dst.contains(cs)) { dst.add(cs); }
			for(FieldSchema f : cs.getFields()) {
				findSubclassSchema(dst, f.getSchema());
			}
		} else if(s instanceof ArraySchema) {
			ArraySchema as = (ArraySchema)s;
			findSubclassSchema(dst, as.getElementSchema(0));
		} else if(s instanceof MapSchema) {
			MapSchema as = (MapSchema)s;
			findSubclassSchema(dst, as.getKeySchema());
			findSubclassSchema(dst, as.getValueSchema());
		}
	}

	private void writeHeader() throws IOException {
		if(schema.getNamespace() != null) {
			line("package "+schema.getNamespace()+";");
			line();
		}
		line("import java.util.*;");
		line("import java.io.*;");
		line("import org.msgpack.*;");
		line("import org.msgpack.schema.ClassSchema;");
		line("import org.msgpack.schema.FieldSchema;");
	}

	private void writeFooter() throws IOException {
		line();
	}

	private void writeClass() throws IOException {
		line();
		line("public final class "+schema.getName()+" implements MessagePackable, MessageMergeable");
		line("{");
		pushIndent();
			writeSchema();
			writeMemberVariables();
			writeMemberFunctions();
		popIndent();
		line("}");
	}

	private void writeSubclass() throws IOException {
		line();
		line("final class "+schema.getName()+" implements MessagePackable, MessageMergeable");
		line("{");
		pushIndent();
			writeSchema();
			writeMemberVariables();
			writeMemberFunctions();
		popIndent();
		line("}");
	}

	private void writeSchema() throws IOException {
		line("private static final ClassSchema _SCHEMA = (ClassSchema)Schema.load(\""+schema.getExpression()+"\");");
		line("public static ClassSchema getSchema() { return _SCHEMA; }");
	}

	private void writeMemberVariables() throws IOException {
		line();
		for(FieldSchema f : schema.getFields()) {
			line("public "+f.getSchema().getFullName()+" "+f.getName()+";");
		}
	}

	private void writeMemberFunctions() throws IOException {
		// void messagePack(Packer pk)
		// boolean equals(Object obj)
		// int hashCode()
		// void set(int _index, Object _value)
		// Object get(int _index);
		// getXxx()
		// setXxx(Xxx xxx)
		writeConstructors();
		writeAccessors();
		writePackFunction();
		writeMergeFunction();
		writeFactoryFunction();
	}

	private void writeConstructors() throws IOException {
		line();
		line("public "+schema.getName()+"() { }");
	}

	private void writeAccessors() throws IOException {
		// FIXME
		//line();
		//for(FieldSchema f : schema.getFields()) {
		//	line("");
		//}
	}

	private void writePackFunction() throws IOException {
		line();
		line("@Override");
		line("public void messagePack(Packer _pk) throws IOException");
		line("{");
		pushIndent();
			line("_pk.packArray("+schema.getFields().length+");");
			line("FieldSchema[] _fields = _SCHEMA.getFields();");
			int i = 0;
			for(FieldSchema f : schema.getFields()) {
				line("_fields["+i+"].getSchema().pack(_pk, "+f.getName()+");");
				++i;
			}
		popIndent();
		line("}");
	}

	private void writeMergeFunction() throws IOException {
		line();
		line("@Override");
		line("@SuppressWarnings(\"unchecked\")");
		line("public void messageMerge(Object obj) throws MessageTypeException");
		line("{");
		pushIndent();
			line("Object[] _source = ((List)obj).toArray();");
			line("FieldSchema[] _fields = _SCHEMA.getFields();");
			int i = 0;
			for(FieldSchema f : schema.getFields()) {
				line("if(_source.length <= "+i+") { return; } this."+f.getName()+" = ("+f.getSchema().getFullName()+")_fields["+i+"].getSchema().convert(_source["+i+"]);");
				++i;
			}
		popIndent();
		line("}");
	}

	private void writeFactoryFunction() throws IOException {
		line();
		line("@SuppressWarnings(\"unchecked\")");
		line("public static "+schema.getName()+" createFromMessage(Object[] _message)");
		line("{");
		pushIndent();
			line(schema.getName()+" _self = new "+schema.getName()+"();");
			int i = 0;
			for(FieldSchema f : schema.getFields()) {
				line("if(_message.length <= "+i+") { return _self; } _self."+f.getName()+" = ("+f.getSchema().getFullName()+")_message["+i+"];");
				++i;
			}
			line("return _self;");
		popIndent();
		line("}");
	}

	private void line(String str) throws IOException {
		for(int i=0; i < indent; ++i) {
			writer.write("\t");
		}
		writer.write(str+"\n");
	}

	private void line() throws IOException {
		writer.write("\n");
	}

	private void pushIndent() {
		indent += 1;
	}

	private void popIndent() {
		indent -= 1;
	}
}

