package org.msgpack.util.codegen;

import static org.msgpack.Templates.tString;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;

import org.junit.Test;
import org.msgpack.MessagePacker;
import org.msgpack.Packer;
import org.msgpack.ReflectionPacker;
import org.msgpack.ReflectionTemplate;
import org.msgpack.Template;
import org.msgpack.Unpacker;

import junit.framework.TestCase;


public class TestDynamicCodeGenPacker extends TestCase {
	public static class StringFieldClass {
		public String s1;
		public String s2;
		public StringFieldClass() { }
	}

	@Test
	public void testPackConvert() throws Exception {
		tString();  // FIXME link StringTemplate

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker.create(StringFieldClass.class);

		StringFieldClass src = new StringFieldClass();

		src.s1 = "kumofs";
		src.s2 = "frsyuki";

		packer.pack(new Packer(out), src);

		Template tmpl = ReflectionTemplate.create(StringFieldClass.class);

		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());

		Object obj = tmpl.unpack(new Unpacker(in));
		assertEquals(obj.getClass(), StringFieldClass.class);

		StringFieldClass dst = (StringFieldClass)obj;
		assertEquals(src.s1, dst.s1);
		assertEquals(src.s2, dst.s2);
	}
}
