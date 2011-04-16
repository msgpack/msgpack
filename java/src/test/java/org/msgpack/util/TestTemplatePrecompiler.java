package org.msgpack.util;

import org.junit.Test;
import static org.junit.Assert.*;
import org.msgpack.MessagePack;
import org.msgpack.MessageTypeException;
import org.msgpack.template.TemplateRegistry;

public class TestTemplatePrecompiler {
 
	@Test
	public void testPrimitiveTypeFields00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DIST, "./target/test-classes");
		Class<?> c = PrimitiveTypeFieldsClass.class;
		TemplatePrecompiler.saveTemplateClass(PrimitiveTypeFieldsClass.class);

		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;

		try {
			MessagePack.pack(src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
			assertTrue(TemplateRegistry.unregister(c));
		}
		try {
			TemplateRegistry.lookup(c, true, true);
			byte[] raw = MessagePack.pack(src);
			PrimitiveTypeFieldsClass dst = MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			//assertEquals(src.f4, dst.f4);
			//assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
		} finally {
			TemplateRegistry.unregister(c);
		}
	}

	@Test
	public void testPrimitiveTypeFields01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DIST, "./target/test-classes");
		Class<?> c = PrimitiveTypeFieldsClass.class;
		TemplatePrecompiler.saveTemplateClass(PrimitiveTypeFieldsClass.class);

		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();

		try {
			MessagePack.pack(src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
			assertTrue(TemplateRegistry.unregister(c));
		}
		try {
			TemplateRegistry.lookup(c, true, true);
			byte[] raw = MessagePack.pack(src);
			PrimitiveTypeFieldsClass dst = MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			//assertEquals(src.f4, dst.f4);
			//assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
		} finally {
			TemplateRegistry.unregister(c);
		}
	}

	@Test
	public void testPrimitiveTypeFields02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DIST, "./target/test-classes");
		Class<?> c = PrimitiveTypeFieldsClass.class;
		TemplatePrecompiler.saveTemplateClass(PrimitiveTypeFieldsClass.class);

		PrimitiveTypeFieldsClass src = null;
		MessagePack.pack(src);
		try {
			TemplateRegistry.lookup(c, true, true);
			byte[] raw = MessagePack.pack(src);
			PrimitiveTypeFieldsClass dst = MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(c);
		}
	}

	public static class PrimitiveTypeFieldsClass {
		public byte f0;
		public short f1;
		public int f2;
		public long f3;
		public float f4;
		public double f5;
		public boolean f6;

		public PrimitiveTypeFieldsClass() {
		}
	}
}
