package org.msgpack;

import static org.msgpack.Templates.*;

import java.util.*;
import java.io.*;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestReflectionPackerTemplate {

	public static class StringFieldClass {
		public String s1;
		public String s2;
		public StringFieldClass() { }
	}

	@Test
	public void testPackConvert() throws Exception {
		tString();

		ByteArrayOutputStream out = new ByteArrayOutputStream();

		MessagePacker packer = ReflectionPacker.create(StringFieldClass.class);

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

