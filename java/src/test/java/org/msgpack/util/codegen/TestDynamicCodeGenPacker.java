package org.msgpack.util.codegen;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;

import org.junit.Test;
import org.msgpack.MessagePacker;
import org.msgpack.MessageUnpacker;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

import junit.framework.TestCase;

public class TestDynamicCodeGenPacker extends TestCase {
	public static class StringFieldClass {
		public String s1;
		public String s2;

		public StringFieldClass() {
		}
	}

	@Test
	public void testPackConvert01() throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker
				.create(StringFieldClass.class);
		MessageUnpacker unpacker = DynamicCodeGenUnpacker
				.create(StringFieldClass.class);

		StringFieldClass src = new StringFieldClass();
		src.s1 = "muga";
		src.s2 = "nishizawa";
		packer.pack(new Packer(out), src);

		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		StringFieldClass dst = (StringFieldClass) new Unpacker(in)
				.unpack(unpacker);
		assertEquals(src.s1, dst.s1);
		assertEquals(src.s2, dst.s2);
	}

	@Test
	public void testPackConvert02() throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker
				.create(StringFieldClass.class);
		Template tmpl = DynamicCodeGenTemplate.create(StringFieldClass.class);

		StringFieldClass src = new StringFieldClass();
		src.s1 = "muga";
		src.s2 = "nishizawa";
		packer.pack(new Packer(out), src);

		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		StringFieldClass dst = (StringFieldClass) tmpl.unpack(new Unpacker(in));
		assertEquals(src.s1, dst.s1);
		assertEquals(src.s2, dst.s2);
	}
}
