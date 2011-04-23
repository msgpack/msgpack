package org.msgpack.util;

import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.junit.Test;
import org.msgpack.MessagePack;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.Optional;
import org.msgpack.template.TemplateBuildException;
import org.msgpack.template.TemplateRegistry;

import junit.framework.TestCase;

public class TestTemplatePrecompilerPackConvert extends TestCase {

	@Test
	public void testPrimitiveTypeFields00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
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
			byte[] raw = MessagePack.pack(src);
			PrimitiveTypeFieldsClass dst = MessagePack.unpack(raw).convert(
					PrimitiveTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
		} finally {
			TemplateRegistry.unregister(PrimitiveTypeFieldsClass.class);
		}
	}

	@Test
	public void testPrimitiveTypeFields01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(PrimitiveTypeFieldsClass.class);

		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();

		try {
			byte[] raw = MessagePack.pack(src);
			PrimitiveTypeFieldsClass dst = MessagePack.unpack(raw).convert(
					PrimitiveTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
		} finally {
			TemplateRegistry.unregister(PrimitiveTypeFieldsClass.class);	
		}
	}

	@Test
	public void testPrimitiveTypeFields02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(PrimitiveTypeFieldsClass.class);

		PrimitiveTypeFieldsClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			PrimitiveTypeFieldsClass dst = MessagePack.unpack(raw).convert(
					PrimitiveTypeFieldsClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(PrimitiveTypeFieldsClass.class);
		}
	}

	@MessagePackMessage
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

	@Test
	public void testOptionalPrimitiveTypeFields00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalPrimitiveTypeFieldsClass.class);

		OptionalPrimitiveTypeFieldsClass src = new OptionalPrimitiveTypeFieldsClass();
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;

		try {
			byte[] raw = MessagePack.pack(src);
			PrimitiveTypeFieldsClass dst = MessagePack.unpack(raw).convert(
					PrimitiveTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
		} finally {
			TemplateRegistry.unregister(OptionalPrimitiveTypeFieldsClass.class);
		}
	}

	@Test
	public void testOptionalPrimitiveTypeFields01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalPrimitiveTypeFieldsClass.class);

		OptionalPrimitiveTypeFieldsClass src = new OptionalPrimitiveTypeFieldsClass();

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalPrimitiveTypeFieldsClass dst = MessagePack.unpack(raw)
					.convert(OptionalPrimitiveTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
		} finally {
			TemplateRegistry.unregister(OptionalPrimitiveTypeFieldsClass.class);	
		}
	}

	@Test
	public void testOptionalPrimitiveTypeFields02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalPrimitiveTypeFieldsClass.class);

		OptionalPrimitiveTypeFieldsClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalPrimitiveTypeFieldsClass dst = MessagePack.unpack(raw)
					.convert(OptionalPrimitiveTypeFieldsClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(OptionalPrimitiveTypeFieldsClass.class);
		}
	}

	@MessagePackMessage
	public static class OptionalPrimitiveTypeFieldsClass {
		@Optional
		public byte f0;
		@Optional
		public short f1;
		@Optional
		public int f2;
		@Optional
		public long f3;
		@Optional
		public float f4;
		@Optional
		public double f5;
		@Optional
		public boolean f6;

		public OptionalPrimitiveTypeFieldsClass() {
		}
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(GeneralReferenceTypeFieldsClass.class);

		GeneralReferenceTypeFieldsClass src = new GeneralReferenceTypeFieldsClass();
		src.f0 = 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = (long) 3;
		src.f4 = (float) 4;
		src.f5 = (double) 5;
		src.f6 = false;
		src.f7 = new BigInteger("7");
		src.f8 = "8";
		src.f9 = new byte[] { 0x01, 0x02 };
		src.f10 = ByteBuffer.wrap("muga".getBytes());

		try {
			byte[] raw = MessagePack.pack(src);
			GeneralReferenceTypeFieldsClass dst = MessagePack.unpack(raw)
					.convert(GeneralReferenceTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
			assertEquals(src.f7, dst.f7);
			assertEquals(src.f8, dst.f8);
			assertEquals(src.f9[0], dst.f9[0]);
			assertEquals(src.f9[1], dst.f9[1]);
			assertEquals(src.f10, dst.f10);
		} finally {
			TemplateRegistry.unregister(GeneralReferenceTypeFieldsClass.class);
		}
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(GeneralReferenceTypeFieldsClass.class);

		GeneralReferenceTypeFieldsClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			GeneralReferenceTypeFieldsClass dst = MessagePack.unpack(raw)
					.convert(GeneralReferenceTypeFieldsClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(GeneralReferenceTypeFieldsClass.class);
		}
	}

	@MessagePackMessage
	public static class GeneralReferenceTypeFieldsClass {
		public Byte f0;
		public Short f1;
		public Integer f2;
		public Long f3;
		public Float f4;
		public Double f5;
		public Boolean f6;
		public BigInteger f7;
		public String f8;
		public byte[] f9;
		public ByteBuffer f10;

		public GeneralReferenceTypeFieldsClass() {
		}
	}

	@Test
	public void testGeneralOptionalReferenceTypeFieldsClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(GeneralOptionalReferenceTypeFieldsClass.class);

		GeneralOptionalReferenceTypeFieldsClass src = new GeneralOptionalReferenceTypeFieldsClass();
		src.f0 = 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = (long) 3;
		src.f4 = (float) 4;
		src.f5 = (double) 5;
		src.f6 = false;
		src.f7 = new BigInteger("7");
		src.f8 = "8";
		src.f9 = new byte[] { 0x01, 0x02 };
		src.f10 = ByteBuffer.wrap("muga".getBytes());

		try {
			byte[] raw = MessagePack.pack(src);
			GeneralOptionalReferenceTypeFieldsClass dst = MessagePack.unpack(
					raw).convert(GeneralOptionalReferenceTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
			assertEquals(src.f7, dst.f7);
			assertEquals(src.f8, dst.f8);
			assertEquals(src.f9[0], dst.f9[0]);
			assertEquals(src.f9[1], dst.f9[1]);
			assertEquals(src.f10, dst.f10);
		} finally {
			TemplateRegistry.unregister(GeneralOptionalReferenceTypeFieldsClass.class);
		}
	}

	@Test
	public void testGeneralOptionalReferenceTypeFieldsClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(GeneralOptionalReferenceTypeFieldsClass.class);

		GeneralOptionalReferenceTypeFieldsClass src = new GeneralOptionalReferenceTypeFieldsClass();
		src.f0 = null;
		src.f1 = null;
		src.f2 = null;
		src.f3 = null;
		src.f4 = null;
		src.f5 = null;
		src.f6 = null;
		src.f7 = null;
		src.f8 = null;
		src.f9 = null;
		src.f10 = null;

		try {
			byte[] raw = MessagePack.pack(src);
			GeneralOptionalReferenceTypeFieldsClass dst = MessagePack.unpack(
					raw).convert(GeneralOptionalReferenceTypeFieldsClass.class);
			assertEquals(src.f0, dst.f0);
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2, dst.f2);
			assertEquals(src.f3, dst.f3);
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5, dst.f5);
			assertEquals(src.f6, dst.f6);
			assertEquals(src.f7, dst.f7);
			assertEquals(src.f8, dst.f8);
			assertEquals(src.f9, dst.f9);
			assertEquals(src.f10, dst.f10);
		} finally {
			TemplateRegistry.unregister(GeneralOptionalReferenceTypeFieldsClass.class);
		}
	}

	@Test
	public void testGeneralOptionalReferenceTypeFieldsClass02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(GeneralOptionalReferenceTypeFieldsClass.class);

		GeneralOptionalReferenceTypeFieldsClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			GeneralOptionalReferenceTypeFieldsClass dst = MessagePack.unpack(
					raw).convert(GeneralOptionalReferenceTypeFieldsClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(GeneralOptionalReferenceTypeFieldsClass.class);
		}
	}

	@MessagePackMessage
	public static class GeneralOptionalReferenceTypeFieldsClass {
		@Optional
		public Byte f0;
		@Optional
		public Short f1;
		@Optional
		public Integer f2;
		@Optional
		public Long f3;
		@Optional
		public Float f4;
		@Optional
		public Double f5;
		@Optional
		public Boolean f6;
		@Optional
		public BigInteger f7;
		@Optional
		public String f8;
		@Optional
		public byte[] f9;
		@Optional
		public ByteBuffer f10;

		public GeneralOptionalReferenceTypeFieldsClass() {
		}
	}

	@Test
	public void testListTypes00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleListNestedType.class);
		TemplatePrecompiler.saveTemplateClass(SampleListTypes.class);

		SampleListTypes src = new SampleListTypes();
		src.f0 = new ArrayList<Integer>();
		src.f1 = new ArrayList<Integer>();
		src.f1.add(1);
		src.f1.add(2);
		src.f1.add(3);
		src.f2 = new ArrayList<String>();
		src.f2.add("e1");
		src.f2.add("e2");
		src.f2.add("e3");
		src.f3 = new ArrayList<List<String>>();
		src.f3.add(src.f2);
		src.f4 = new ArrayList<SampleListNestedType>();
		SampleListNestedType slnt = new SampleListNestedType();
		slnt.f0 = new byte[] { 0x01, 0x02 };
		slnt.f1 = "muga";
		src.f4.add(slnt);
		src.f5 = new ArrayList<ByteBuffer>();
		src.f5.add(ByteBuffer.wrap("e1".getBytes()));
		src.f5.add(ByteBuffer.wrap("e2".getBytes()));
		src.f5.add(ByteBuffer.wrap("e3".getBytes()));

		try {
			byte[] raw = MessagePack.pack(src);
			SampleListTypes dst = MessagePack.unpack(raw).convert(
					SampleListTypes.class);
			for (int i = 0; i < src.f1.size(); ++i) {
				assertEquals(src.f1.get(i), dst.f1.get(i));
			}
			assertEquals(src.f2.size(), dst.f2.size());
			for (int i = 0; i < src.f2.size(); ++i) {
				assertEquals(src.f2.get(i), dst.f2.get(i));
			}
			assertEquals(src.f3.size(), dst.f3.size());
			for (int i = 0; i < src.f3.size(); ++i) {
				List<String> srclist = src.f3.get(i);
				List<String> dstlist = dst.f3.get(i);
				assertEquals(srclist.size(), dstlist.size());
				for (int j = 0; j < srclist.size(); ++j) {
					assertEquals(srclist.get(j), dstlist.get(j));
				}
			}
			assertEquals(src.f4.size(), dst.f4.size());
			for (int i = 0; i < src.f4.size(); ++i) {
				SampleListNestedType s = src.f4.get(i);
				SampleListNestedType d = dst.f4.get(i);
				assertEquals(s.f0[0], d.f0[0]);
				assertEquals(s.f0[1], d.f0[1]);
				assertEquals(s.f1, d.f1);
			}
			assertEquals(src.f5.size(), dst.f5.size());
			for (int i = 0; i < src.f5.size(); ++i) {
				ByteBuffer s = src.f5.get(i);
				ByteBuffer d = dst.f5.get(i);
				assertEquals(s, d);
			}
		} finally {
			TemplateRegistry.unregister(SampleListNestedType.class);
			TemplateRegistry.unregister(SampleListTypes.class);
		}
	}

	@Test
	public void testListTypes01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleListNestedType.class);
		TemplatePrecompiler.saveTemplateClass(SampleListTypes.class);

		SampleListTypes src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleListTypes dst = MessagePack.unpack(raw).convert(
					SampleListTypes.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(SampleListNestedType.class);
			TemplateRegistry.unregister(SampleListTypes.class);
		}
	}

	@MessagePackMessage
	public static class SampleListTypes {
		public List<Integer> f0;
		public List<Integer> f1;
		public List<String> f2;
		public List<List<String>> f3;
		public List<SampleListNestedType> f4;
		public List<ByteBuffer> f5;

		public SampleListTypes() {
		}
	}

	@MessagePackMessage
	public static class SampleListNestedType {
		public byte[] f0;
		public String f1;

		public SampleListNestedType() {
		}
	}

	@Test
	public void testOptionalListTypes00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalListNestedType.class);
		TemplatePrecompiler.saveTemplateClass(SampleOptionalListTypes.class);

		SampleOptionalListTypes src = new SampleOptionalListTypes();
		src.f0 = new ArrayList<Integer>();
		src.f1 = new ArrayList<Integer>();
		src.f1.add(1);
		src.f1.add(2);
		src.f1.add(3);
		src.f2 = new ArrayList<String>();
		src.f2.add("e1");
		src.f2.add("e2");
		src.f2.add("e3");
		src.f3 = new ArrayList<List<String>>();
		src.f3.add(src.f2);
		src.f4 = new ArrayList<SampleOptionalListNestedType>();
		SampleOptionalListNestedType slnt = new SampleOptionalListNestedType();
		slnt.f0 = new byte[] { 0x01, 0x02 };
		slnt.f1 = "muga";
		src.f4.add(slnt);
		src.f5 = new ArrayList<ByteBuffer>();
		src.f5.add(ByteBuffer.wrap("e1".getBytes()));
		src.f5.add(ByteBuffer.wrap("e2".getBytes()));
		src.f5.add(ByteBuffer.wrap("e3".getBytes()));

		try {
			byte[] raw = MessagePack.pack(src);
			SampleOptionalListTypes dst = MessagePack.unpack(raw).convert(
					SampleOptionalListTypes.class);
			assertEquals(src.f0.size(), dst.f0.size());
			assertEquals(src.f1.size(), dst.f1.size());
			for (int i = 0; i < src.f1.size(); ++i) {
				assertEquals(src.f1.get(i), dst.f1.get(i));
			}
			assertEquals(src.f2.size(), dst.f2.size());
			for (int i = 0; i < src.f2.size(); ++i) {
				assertEquals(src.f2.get(i), dst.f2.get(i));
			}
			assertEquals(src.f3.size(), dst.f3.size());
			for (int i = 0; i < src.f3.size(); ++i) {
				List<String> srclist = src.f3.get(i);
				List<String> dstlist = dst.f3.get(i);
				assertEquals(srclist.size(), dstlist.size());
				for (int j = 0; j < srclist.size(); ++j) {
					assertEquals(srclist.get(j), dstlist.get(j));
				}
			}
			assertEquals(src.f4.size(), dst.f4.size());
			for (int i = 0; i < src.f4.size(); ++i) {
				SampleOptionalListNestedType s = src.f4.get(i);
				SampleOptionalListNestedType d = dst.f4.get(i);
				assertEquals(s.f0[0], d.f0[0]);
				assertEquals(s.f0[1], d.f0[1]);
				assertEquals(s.f1, d.f1);
			}
			assertEquals(src.f5.size(), dst.f5.size());
			for (int i = 0; i < src.f5.size(); ++i) {
				ByteBuffer s = src.f5.get(i);
				ByteBuffer d = dst.f5.get(i);
				assertEquals(s, d);
			}
		} finally {
			TemplateRegistry.unregister(SampleOptionalListNestedType.class);
			TemplateRegistry.unregister(SampleOptionalListNestedType.class);
		}
	}

	@Test
	public void testOptionalListTypes01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalListNestedType.class);
		TemplatePrecompiler.saveTemplateClass(SampleOptionalListTypes.class);

		SampleOptionalListTypes src = new SampleOptionalListTypes();
		src.f0 = new ArrayList<Integer>();
		src.f1 = null;
		src.f2 = new ArrayList<String>();
		src.f3 = new ArrayList<List<String>>();
		src.f4 = null;
		src.f5 = new ArrayList<ByteBuffer>();

		try {
			byte[] raw = MessagePack.pack(src);
			SampleOptionalListTypes dst = MessagePack.unpack(raw).convert(
					SampleOptionalListTypes.class);
			assertEquals(src.f0.size(), dst.f0.size());
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2.size(), dst.f2.size());
			assertEquals(src.f3.size(), dst.f3.size());
			assertEquals(src.f4, dst.f4);
			assertEquals(src.f5.size(), dst.f5.size());
		} finally {
			TemplateRegistry.unregister(SampleOptionalListNestedType.class);
			TemplateRegistry.unregister(SampleOptionalListNestedType.class);
		}
	}

	@Test
	public void testOptionalListTypes02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalListNestedType.class);
		TemplatePrecompiler.saveTemplateClass(SampleOptionalListTypes.class);

		SampleListTypes src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleListTypes dst = MessagePack.unpack(raw).convert(
					SampleListTypes.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(SampleOptionalListNestedType.class);
			TemplateRegistry.unregister(SampleOptionalListNestedType.class);
		}
	}

	@MessagePackMessage
	public static class SampleOptionalListTypes {
		@Optional
		public List<Integer> f0;
		@Optional
		public List<Integer> f1;
		@Optional
		public List<String> f2;
		@Optional
		public List<List<String>> f3;
		@Optional
		public List<SampleOptionalListNestedType> f4;
		@Optional
		public List<ByteBuffer> f5;

		public SampleOptionalListTypes() {
		}
	}

	@MessagePackMessage
	public static class SampleOptionalListNestedType {
		@Optional
		public byte[] f0;
		@Optional
		public String f1;

		public SampleOptionalListNestedType() {
		}
	}

	@Test
	public void testMapTypes00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleMapTypes.class);

		SampleMapTypes src = new SampleMapTypes();
		src.f0 = new HashMap<Integer, Integer>();
		src.f1 = new HashMap<Integer, Integer>();
		src.f1.put(1, 1);
		src.f1.put(2, 2);
		src.f1.put(3, 3);
		src.f2 = new HashMap<String, Integer>();
		src.f2.put("k1", 1);
		src.f2.put("k2", 2);
		src.f2.put("k3", 3);

		try {
			byte[] raw = MessagePack.pack(src);
			SampleMapTypes dst = MessagePack.unpack(raw).convert(
					SampleMapTypes.class);
			assertEquals(0, dst.f0.size());
			assertEquals(src.f1.size(), dst.f1.size());
			Iterator<Integer> srcf1 = src.f1.keySet().iterator();
			while (srcf1.hasNext()) {
				Integer s1 = srcf1.next();
				assertEquals(src.f1.get(s1), dst.f1.get(s1));
			}
			assertEquals(src.f2.size(), dst.f2.size());
			Iterator<String> srcf2 = src.f2.keySet().iterator();
			while (srcf2.hasNext()) {
				String s2 = srcf2.next();
				assertEquals(src.f2.get(s2), dst.f2.get(s2));
			}
		} finally {
			TemplateRegistry.unregister(SampleMapTypes.class);
		}
	}

	@Test
	public void testMapTypes01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleMapTypes.class);

		SampleMapTypes src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleMapTypes dst = MessagePack.unpack(raw).convert(SampleMapTypes.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(SampleMapTypes.class);
		}
	}

	@MessagePackMessage
	public static class SampleMapTypes {
		public Map<Integer, Integer> f0;
		public Map<Integer, Integer> f1;
		public Map<String, Integer> f2;

		public SampleMapTypes() {
		}
	}

	@Test
	public void testOptionalMapTypes00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalMapTypes.class);

		SampleOptionalMapTypes src = new SampleOptionalMapTypes();
		src.f0 = new HashMap<Integer, Integer>();
		src.f1 = new HashMap<Integer, Integer>();
		src.f1.put(1, 1);
		src.f1.put(2, 2);
		src.f1.put(3, 3);
		src.f2 = new HashMap<String, Integer>();
		src.f2.put("k1", 1);
		src.f2.put("k2", 2);
		src.f2.put("k3", 3);

		try {
			byte[] raw = MessagePack.pack(src);
			SampleOptionalMapTypes dst = MessagePack.unpack(raw).convert(
					SampleOptionalMapTypes.class);
			assertEquals(0, dst.f0.size());
			assertEquals(src.f1.size(), dst.f1.size());
			Iterator<Integer> srcf1 = src.f1.keySet().iterator();
			while (srcf1.hasNext()) {
				Integer s1 = srcf1.next();
				assertEquals(src.f1.get(s1), dst.f1.get(s1));
			}
			assertEquals(src.f2.size(), dst.f2.size());
			Iterator<String> srcf2 = src.f2.keySet().iterator();
			while (srcf2.hasNext()) {
				String s2 = srcf2.next();
				assertEquals(src.f2.get(s2), dst.f2.get(s2));
			}
		} finally {
			TemplateRegistry.unregister(SampleOptionalMapTypes.class);
		}
	}

	@Test
	public void testOptionalMapTypes01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalMapTypes.class);

		SampleOptionalMapTypes src = new SampleOptionalMapTypes();
		src.f0 = new HashMap<Integer, Integer>();
		src.f1 = null;
		src.f2 = new HashMap<String, Integer>();

		try {
			byte[] raw = MessagePack.pack(src);
			SampleOptionalMapTypes dst = MessagePack.unpack(raw).convert(
					SampleOptionalMapTypes.class);
			assertEquals(src.f0.size(), dst.f0.size());
			assertEquals(src.f1, dst.f1);
			assertEquals(src.f2.size(), dst.f2.size());
		} finally {
			TemplateRegistry.unregister(SampleOptionalMapTypes.class);
		}
	}

	@Test
	public void testOptionalMapTypes02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalMapTypes.class);

		SampleOptionalMapTypes src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleOptionalMapTypes dst = MessagePack.unpack(raw).convert(
					SampleOptionalMapTypes.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(SampleOptionalMapTypes.class);
		}
	}

	@MessagePackMessage
	public static class SampleOptionalMapTypes {
		@Optional
		public Map<Integer, Integer> f0;
		@Optional
		public Map<Integer, Integer> f1;
		@Optional
		public Map<String, Integer> f2;

		public SampleOptionalMapTypes() {
		}
	}

	@Test
	public void testFinalClass() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		try {
			TemplatePrecompiler.saveTemplateClass(FinalModifierClass.class);
			assertTrue(true);
		} catch (TemplateBuildException e) {
			fail();
		} finally {
			TemplateRegistry.unregister(FinalModifierClass.class);
		}
	}

	@MessagePackMessage
	public final static class FinalModifierClass {
	}

	@MessagePackMessage
	public abstract static class AbstractModifierClass {
	}

	@Test
	public void testInterfaceType00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		try {
			TemplatePrecompiler.saveTemplateClass(SampleInterface.class);
			fail();
		} catch (Throwable t) {
			assertTrue(t instanceof TemplateBuildException);
		} finally {
			TemplateRegistry.unregister(SampleInterface.class);
		}
	}

	@MessagePackMessage
	public interface SampleInterface {
	}

	@Test
	public void testFieldModifiers() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(FieldModifiersClass.class);

		FieldModifiersClass src = new FieldModifiersClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;

		try {
			byte[] raw = MessagePack.pack(src);
			FieldModifiersClass dst = MessagePack.unpack(raw).convert(
					FieldModifiersClass.class);
			assertTrue(src.f1 == dst.f1);
			assertTrue(src.f2 != dst.f2);
			assertTrue(src.f3 != dst.f3);
			assertTrue(src.f4 != dst.f4);
		} finally {
			TemplateRegistry.unregister(FieldModifiersClass.class);	
		}
	}

	@MessagePackMessage
	public static class FieldModifiersClass {
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public FieldModifiersClass() {
		}
	}

	@Test
	public void testOptionalFieldModifiers() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalFieldModifiersClass.class);

		OptionalFieldModifiersClass src = new OptionalFieldModifiersClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalFieldModifiersClass dst = MessagePack.unpack(raw).convert(
					OptionalFieldModifiersClass.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1 == dst.f1);
			assertTrue(src.f2 != dst.f2);
			assertTrue(src.f3 != dst.f3);
			assertTrue(src.f4 != dst.f4);
		} finally {
			TemplateRegistry.unregister(OptionalFieldModifiersClass.class);
		}
	}

	@MessagePackMessage
	public static class OptionalFieldModifiersClass {
		@Optional
		public int f0;
		@Optional
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public OptionalFieldModifiersClass() {
		}
	}

	@Test
	public void testNestedFieldClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(NestedClass.class);
		TemplatePrecompiler.saveTemplateClass(BaseClass.class);

		BaseClass src = new BaseClass();
		NestedClass src2 = new NestedClass();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		try {
			byte[] raw = MessagePack.pack(src);
			BaseClass dst = MessagePack.unpack(raw).convert(BaseClass.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1.f2 == dst.f1.f2);
		} finally {
			TemplateRegistry.unregister(NestedClass.class);
			TemplateRegistry.unregister(BaseClass.class);
		}
	}

	@Test
	public void testNestedFieldClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(NestedClass.class);
		TemplatePrecompiler.saveTemplateClass(BaseClass.class);

		BaseClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			BaseClass dst = MessagePack.unpack(raw).convert(BaseClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(NestedClass.class);
			TemplateRegistry.unregister(BaseClass.class);
		}
	}

	@MessagePackMessage
	public static class BaseClass {
		public int f0;
		public NestedClass f1;

		public BaseClass() {
		}
	}

	@MessagePackMessage
	public static class NestedClass {
		public int f2;

		public NestedClass() {
		}
	}

	@Test
	public void testOptionalNestedFieldClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalNestedClass.class);
		TemplatePrecompiler.saveTemplateClass(OptionalBaseClass.class);

		OptionalBaseClass src = new OptionalBaseClass();
		OptionalNestedClass src2 = new OptionalNestedClass();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalBaseClass dst = MessagePack.unpack(raw).convert(
					OptionalBaseClass.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1.f2 == dst.f1.f2);
		} finally {
			TemplateRegistry.unregister(OptionalNestedClass.class);
			TemplateRegistry.unregister(OptionalBaseClass.class);
		}
	}

	@Test
	public void testOptionalNestedFieldClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalNestedClass.class);
		TemplatePrecompiler.saveTemplateClass(OptionalBaseClass.class);

		OptionalBaseClass src = new OptionalBaseClass();
		src.f1 = null;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalBaseClass dst = MessagePack.unpack(raw).convert(
					OptionalBaseClass.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1 == dst.f1);
		} finally {
			TemplateRegistry.unregister(OptionalNestedClass.class);
			TemplateRegistry.unregister(OptionalBaseClass.class);
		}
	}

	@Test
	public void testOptionalNestedFieldClass02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalNestedClass.class);
		TemplatePrecompiler.saveTemplateClass(OptionalBaseClass.class);

		OptionalBaseClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalBaseClass dst = MessagePack.unpack(raw).convert(
					OptionalBaseClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(OptionalNestedClass.class);
			TemplateRegistry.unregister(OptionalBaseClass.class);
		}
	}

	@MessagePackMessage
	public static class OptionalBaseClass {
		@Optional
		public int f0;
		@Optional
		public OptionalNestedClass f1;

		public OptionalBaseClass() {
		}
	}

	@MessagePackMessage
	public static class OptionalNestedClass {
		@Optional
		public int f2;

		public OptionalNestedClass() {
		}
	}

	@Test
	public void testMessagePackMessageFieldClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(MessagePackMessageClass2.class);
		TemplatePrecompiler.saveTemplateClass(BaseClass2.class);

		BaseClass2 src = new BaseClass2();
		MessagePackMessageClass2 src2 = new MessagePackMessageClass2();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		try {
			byte[] raw = MessagePack.pack(src);
			BaseClass2 dst = MessagePack.unpack(raw).convert(BaseClass2.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1.f2 == dst.f1.f2);
		} finally {
			TemplateRegistry.unregister(MessagePackMessageClass2.class);
			TemplateRegistry.unregister(BaseClass2.class);
		}
	}

	@Test
	public void testMessagePackMessageFieldClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(MessagePackMessageClass2.class);
		TemplatePrecompiler.saveTemplateClass(BaseClass2.class);

		BaseClass2 src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			BaseClass2 dst = MessagePack.unpack(raw).convert(BaseClass2.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(MessagePackMessageClass2.class);
			TemplateRegistry.unregister(BaseClass2.class);
		}
	}

	@MessagePackMessage
	public static class BaseClass2 {
		public int f0;
		public MessagePackMessageClass2 f1;

		public BaseClass2() {
		}
	}

	@MessagePackMessage
	public static class MessagePackMessageClass2 {
		public int f2;

		public MessagePackMessageClass2() {
		}
	}

	@Test
	public void testOptionalMessagePackMessageFieldClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalBaseClass2.class);
		TemplatePrecompiler.saveTemplateClass(OptionalMessagePackMessageClass2.class);

		OptionalBaseClass2 src = new OptionalBaseClass2();
		OptionalMessagePackMessageClass2 src2 = new OptionalMessagePackMessageClass2();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalBaseClass2 dst = MessagePack.unpack(raw).convert(
					OptionalBaseClass2.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1.f2 == dst.f1.f2);
		} finally {
			TemplateRegistry.unregister(OptionalBaseClass2.class);
			TemplateRegistry.unregister(OptionalMessagePackMessageClass2.class);
		}
	}

	@Test
	public void testOptionalMessagePackMessageFieldClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalBaseClass2.class);
		TemplatePrecompiler.saveTemplateClass(OptionalMessagePackMessageClass2.class);

		OptionalBaseClass2 src = new OptionalBaseClass2();
		src.f1 = null;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalBaseClass2 dst = MessagePack.unpack(raw).convert(
					OptionalBaseClass2.class);
			assertTrue(src.f0 == dst.f0);
			assertEquals(src.f1, dst.f1);
		} finally {
			TemplateRegistry.unregister(OptionalBaseClass2.class);
			TemplateRegistry.unregister(OptionalMessagePackMessageClass2.class);
		}
	}

	@Test
	public void testOptionalMessagePackMessageFieldClass02() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(OptionalBaseClass2.class);
		TemplatePrecompiler.saveTemplateClass(OptionalMessagePackMessageClass2.class);

		OptionalBaseClass2 src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			OptionalBaseClass2 dst = MessagePack.unpack(raw).convert(
					OptionalBaseClass2.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(OptionalBaseClass2.class);
			TemplateRegistry.unregister(OptionalMessagePackMessageClass2.class);
		}
	}

	@MessagePackMessage
	public static class OptionalBaseClass2 {
		@Optional
		public int f0;
		@Optional
		public OptionalMessagePackMessageClass2 f1;

		public OptionalBaseClass2() {
		}
	}

	@MessagePackMessage
	public static class OptionalMessagePackMessageClass2 {
		@Optional
		public int f2;

		public OptionalMessagePackMessageClass2() {
		}
	}

	@Test
	public void testExtendedClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleSuperClass.class);
		TemplatePrecompiler.saveTemplateClass(SampleSubClass.class);

		SampleSubClass src = new SampleSubClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f8 = 8;
		src.f9 = 9;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleSubClass dst = MessagePack.unpack(raw).convert(
					SampleSubClass.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1 == dst.f1);
			assertTrue(src.f2 != dst.f2);
			assertTrue(src.f3 != dst.f3);
			assertTrue(src.f4 != dst.f4);
			assertTrue(src.f5 == dst.f5);
			assertTrue(src.f6 == dst.f6);
			assertTrue(src.f8 != dst.f8);
			assertTrue(src.f9 != dst.f9);
		} finally {
			TemplateRegistry.unregister(SampleSuperClass.class);
			TemplateRegistry.unregister(SampleSubClass.class);
		}
	}

	@Test
	public void testExtendedClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleSuperClass.class);
		TemplatePrecompiler.saveTemplateClass(SampleSubClass.class);

		SampleSubClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleSubClass dst = MessagePack.unpack(raw).convert(
					SampleSubClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(SampleSuperClass.class);
			TemplateRegistry.unregister(SampleSubClass.class);
		}
	}

	@MessagePackMessage
	public static class SampleSubClass extends SampleSuperClass {
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public SampleSubClass() {
		}
	}

	@MessagePackMessage
	public static class SampleSuperClass {
		public int f5;
		public final int f6 = 2;
		@SuppressWarnings("unused")
		private int f7;
		protected int f8;
		int f9;

		public SampleSuperClass() {
		}
	}

	@Test
	public void testOptionalExtendedClass00() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalSuperClass.class);
		TemplatePrecompiler.saveTemplateClass(SampleOptionalSubClass.class);

		SampleOptionalSubClass src = new SampleOptionalSubClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f8 = 8;
		src.f9 = 9;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleOptionalSubClass dst = MessagePack.unpack(raw).convert(
					SampleOptionalSubClass.class);
			assertTrue(src.f0 == dst.f0);
			assertTrue(src.f1 == dst.f1);
			assertTrue(src.f2 != dst.f2);
			assertTrue(src.f3 != dst.f3);
			assertTrue(src.f4 != dst.f4);
			assertTrue(src.f5 == dst.f5);
			assertTrue(src.f6 == dst.f6);
			assertTrue(src.f8 != dst.f8);
			assertTrue(src.f9 != dst.f9);
		} finally {
			TemplateRegistry.unregister(SampleOptionalSuperClass.class);
			TemplateRegistry.unregister(SampleOptionalSubClass.class);
		}
	}

	@Test
	public void testOptionalExtendedClass01() throws Exception {
		System.getProperties().setProperty(TemplatePrecompiler.DEST, "./target/test-classes");
		TemplatePrecompiler.saveTemplateClass(SampleOptionalSuperClass.class);
		TemplatePrecompiler.saveTemplateClass(SampleOptionalSubClass.class);

		SampleOptionalSubClass src = null;

		try {
			byte[] raw = MessagePack.pack(src);
			SampleOptionalSubClass dst = MessagePack.unpack(raw).convert(
					SampleOptionalSubClass.class);
			assertEquals(src, dst);
		} finally {
			TemplateRegistry.unregister(SampleOptionalSuperClass.class);
			TemplateRegistry.unregister(SampleOptionalSubClass.class);
		}
	}

	@MessagePackMessage
	public static class SampleOptionalSubClass extends SampleOptionalSuperClass {
		@Optional
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public SampleOptionalSubClass() {
		}
	}

	@MessagePackMessage
	public static class SampleOptionalSuperClass {
		@Optional
		public int f5;
		public final int f6 = 2;
		@SuppressWarnings("unused")
		private int f7;
		protected int f8;
		int f9;

		public SampleOptionalSuperClass() {
		}
	}
}
