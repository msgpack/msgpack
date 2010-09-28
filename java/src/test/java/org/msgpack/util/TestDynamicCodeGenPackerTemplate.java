package org.msgpack.util;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;

import org.junit.Test;
import org.msgpack.CustomPacker;
import org.msgpack.MessagePacker;
import org.msgpack.Packer;
import org.msgpack.ReflectionTemplate;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.util.codegen.DynamicCodeGenPacker;
import org.msgpack.util.codegen.DynamicCodeGenTemplate;

import static org.junit.Assert.*;

public class TestDynamicCodeGenPackerTemplate {

	public static class StringFieldClass {
		public String s1;
		public String s2;
		public StringFieldClass() { }
	}

	@Test
	public void testPackConvert() throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();

		MessagePacker packer = DynamicCodeGenPacker.create(StringFieldClass.class);

		StringFieldClass src = new StringFieldClass();

		src.s1 = "kumofs";
		src.s2 = "frsyuki";

		packer.pack(new Packer(out), src);

		Template tmpl = DynamicCodeGenTemplate.create(StringFieldClass.class);

		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());

		Object obj = tmpl.unpack(new Unpacker(in));
		assertEquals(obj.getClass(), StringFieldClass.class);

		StringFieldClass dst = (StringFieldClass)obj;
		assertEquals(src.s1, dst.s1);
		assertEquals(src.s2, dst.s2);
	}

	@Test
	public void testPackConvert02() throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();

		CustomPacker.register(StringFieldClass.class, DynamicCodeGenPacker.create(StringFieldClass.class));
				

		StringFieldClass src = new StringFieldClass();

		src.s1 = "kumofs";
		src.s2 = "frsyuki";

		new Packer(out).pack(src);

		Template tmpl = ReflectionTemplate.create(StringFieldClass.class);

		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());

		Object obj = tmpl.unpack(new Unpacker(in));
		assertEquals(obj.getClass(), StringFieldClass.class);

		StringFieldClass dst = (StringFieldClass)obj;
		assertEquals(src.s1, dst.s1);
		assertEquals(src.s2, dst.s2);
	}
}

