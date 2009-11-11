package org.msgpack.schema;

import java.util.ArrayList;
import java.util.List;
import java.io.IOException;
import java.io.File;
import java.io.FileOutputStream;
import java.io.Writer;

public class ClassGenerator {
	private ClassSchema schema;
	private Writer writer;
	private int indent;

	private ClassGenerator(Writer writer)
	{
		this.writer = writer;
		this.indent = 0;
	}

	public static void write(Schema schema, Writer dest) throws IOException
	{
		if(!(schema instanceof ClassSchema)) {
			throw new RuntimeException("schema is not class schema");
		}
		ClassSchema cs = (ClassSchema)schema;
		new ClassGenerator(dest).run(cs);
	}

	private void run(ClassSchema cs) throws IOException
	{
		List<ClassSchema> subclasses = new ArrayList<ClassSchema>();
		for(FieldSchema f : cs.getFields()) {
			findSubclassSchema(subclasses, f.getType());
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

	private void findSubclassSchema(List<ClassSchema> dst, Schema s)
	{
		if(s instanceof ClassSchema) {
			ClassSchema cs = (ClassSchema)s;
			if(!dst.contains(cs)) { dst.add(cs); }
			for(FieldSchema f : cs.getFields()) {
				findSubclassSchema(dst, f.getType());
			}
		} else if(s instanceof ArraySchema) {
			ArraySchema as = (ArraySchema)s;
			findSubclassSchema(dst, as.getElementType());
		} else if(s instanceof MapSchema) {
			MapSchema as = (MapSchema)s;
			findSubclassSchema(dst, as.getKeyType());
			findSubclassSchema(dst, as.getValueType());
		}
	}

	private void writeHeader() throws IOException
	{
		if(schema.getNamespace() != null) {
			line("package "+schema.getNamespace()+";");
			line();
		}
		line("import java.util.*;");
		line("import java.io.*;");
		line("import org.msgpack.*;");
		line("import org.msgpack.schema.*;");
	}

	private void writeFooter() throws IOException
	{
	}

	private void writeClass() throws IOException
	{
		line();
		line("public final class "+schema.getName()+" implements MessagePackable, MessageConvertable");
		line("{");
		pushIndent();
			writeSchema();
			writeMemberVariables();
			writeMemberFunctions();
		popIndent();
		line("}");
	}

	private void writeSubclass() throws IOException
	{
		line();
		line("final class "+schema.getName()+" implements MessagePackable, MessageConvertable");
		line("{");
		pushIndent();
			writeSchema();
			writeMemberVariables();
			writeMemberFunctions();
		popIndent();
		line("}");
	}

	private void writeSchema() throws IOException
	{
		line("private static final ClassSchema _SCHEMA = (ClassSchema)Schema.load(\""+schema.getExpression()+"\");");
		line("public static ClassSchema getSchema() { return _SCHEMA; }");
	}

	private void writeMemberVariables() throws IOException
	{
		line();
		for(FieldSchema f : schema.getFields()) {
			line("public "+f.getType().getFullName()+" "+f.getName()+";");
		}
	}

	private void writeMemberFunctions() throws IOException
	{
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
		writeConvertFunction();
	}

	private void writeConstructors() throws IOException
	{
		line();
		line("public "+schema.getName()+"() { }");
	}

	private void writeAccessors() throws IOException
	{
		// FIXME
		//line();
		//for(FieldSchema f : schema.getFields()) {
		//	line("");
		//}
	}

	private void writePackFunction() throws IOException
	{
		line();
		line("@Override");
		line("public void messagePack(Packer pk) throws IOException");
		line("{");
		pushIndent();
			line("List<? extends FieldSchema> _f = _SCHEMA.getFields();");
			line("pk.packArray("+schema.getFields().size()+");");
			int i = 0;
			for(FieldSchema f : schema.getFields()) {
				line("_f.get("+i+").getType().pack(pk, "+f.getName()+");");
				++i;
			}
		popIndent();
		line("}");
	}

	private void writeConvertFunction() throws IOException
	{
		line();
		line("@Override");
		line("@SuppressWarnings(\"unchecked\")");
		line("public void messageConvert(GenericObject obj)");
		line("{");
		pushIndent();
			line("List<GenericObject> _l = obj.asArray();");
			line("List<? extends FieldSchema> _f = _SCHEMA.getFields();");
			int i = 0;
			for(FieldSchema f : schema.getFields()) {
				line("if(_l.size() <= "+i+") { return; } "+f.getName()+" = ("+f.getType().getFullName()+")_f.get("+i+").getType().convert(_l.get("+i+"));");
				++i;
			}
		popIndent();
		line("}");
		line();
		line("public static "+schema.getName()+" convert(GenericObject obj)");
		line("{");
		pushIndent();
			line("return ("+schema.getName()+")_SCHEMA.convert(obj);");
		popIndent();
		line("}");
	}

	private void line(String str) throws IOException
	{
		for(int i=0; i < indent; ++i) {
			writer.write("\t");
		}
		writer.write(str+"\n");
	}

	private void line() throws IOException
	{
		writer.write("\n");
	}

	private void pushIndent()
	{
		indent += 1;
	}

	private void popIndent()
	{
		indent -= 1;
	}
}

