package org.msgpack.template;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import org.msgpack.MessagePack;
import org.msgpack.MessagePackable;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.msgpack.annotation.Optional;

import junit.framework.TestCase;

public class TestTemplateBuilderPackUnpack extends TestCase {
	static {
		MessagePack.register(PrimitiveTypeFieldsClass.class);
		MessagePack.register(OptionalPrimitiveTypeFieldsClass.class);
		MessagePack.register(GeneralReferenceTypeFieldsClass.class);
		MessagePack.register(GeneralOptionalReferenceTypeFieldsClass.class);
		MessagePack.register(SampleListTypes.class);
		MessagePack.register(SampleOptionalListTypes.class);
		MessagePack.register(SampleMapTypes.class);
		MessagePack.register(SampleOptionalMapTypes.class);
		MessagePack.register(SampleEnumFieldClass.class);
		MessagePack.register(SampleOptionalEnumFieldClass.class);
		MessagePack.register(FieldModifiersClass.class);
		MessagePack.register(OptionalFieldModifiersClass.class);
		MessagePack.register(BaseClass.class);
		MessagePack.register(NestedClass.class);
		MessagePack.register(BaseClass2.class);
		MessagePack.register(OptionalBaseClass.class);
		MessagePack.register(OptionalNestedClass.class);
		MessagePack.register(OptionalBaseClass2.class);
		MessagePack.register(SampleSubClass.class);
		MessagePack.register(SampleSuperClass.class);
		MessagePack.register(SampleOptionalSubClass.class);
		MessagePack.register(SampleOptionalSuperClass.class);
		MessagePack.register(BaseMessagePackableUnpackableClass.class);
		MessagePack.register(MessagePackableUnpackableClass.class);
		MessagePack.register(OptionalBaseMessagePackableUnpackableClass.class);
		MessagePack.register(OptionalMessagePackableUnpackableClass.class);
	}

	@Test
	public void testPrimitiveTypeFields00() throws Exception {
		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;

		byte[] raw = MessagePack.pack(src);

		PrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5, dst.f5);
		assertEquals(src.f6, dst.f6);
	}

	@Test
	public void testPrimitiveTypeFields01() throws Exception {
		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();

		byte[] raw = MessagePack.pack(src);

		PrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5, dst.f5);
		assertEquals(src.f6, dst.f6);
	}

	@Test
	public void testPrimitiveTypeFields02() throws Exception {
		PrimitiveTypeFieldsClass src = null;

		byte[] raw = MessagePack.pack(src);

		PrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
		assertEquals(src, dst);
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

	@Test
	public void testOptionalPrimitiveTypeFields00() throws Exception {
		OptionalPrimitiveTypeFieldsClass src = new OptionalPrimitiveTypeFieldsClass();
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;

		byte[] raw = MessagePack.pack(src);

		PrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5, dst.f5);
		assertEquals(src.f6, dst.f6);
	}

	@Test
	public void testOptionalPrimitiveTypeFields01() throws Exception {
		OptionalPrimitiveTypeFieldsClass src = new OptionalPrimitiveTypeFieldsClass();

		byte[] raw = MessagePack.pack(src);

		OptionalPrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, OptionalPrimitiveTypeFieldsClass.class);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5, dst.f5);
		assertEquals(src.f6, dst.f6);
	}

	@Test
	public void testOptionalPrimitiveTypeFields02() throws Exception {
		OptionalPrimitiveTypeFieldsClass src = null;

		byte[] raw = MessagePack.pack(src);

		OptionalPrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, OptionalPrimitiveTypeFieldsClass.class);
		assertEquals(src, dst);
	}

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

		byte[] raw = MessagePack.pack(src);

		GeneralReferenceTypeFieldsClass dst =
			MessagePack.unpack(raw, GeneralReferenceTypeFieldsClass.class);
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
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass01() throws Exception {
		GeneralReferenceTypeFieldsClass src = null;

		byte[] raw = MessagePack.pack(src);

		GeneralReferenceTypeFieldsClass dst =
			MessagePack.unpack(raw, GeneralReferenceTypeFieldsClass.class);
		assertEquals(src, dst);
	}

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
	public void testGeneralOptionalReferenceTypeFieldsClass00()
			throws Exception {
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

		byte[] raw = MessagePack.pack(src);

		GeneralOptionalReferenceTypeFieldsClass dst =
			MessagePack.unpack(raw, GeneralOptionalReferenceTypeFieldsClass.class);
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
	}

	@Test
	public void testGeneralOptionalReferenceTypeFieldsClass01()
			throws Exception {
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

		byte[] raw = MessagePack.pack(src);

		GeneralOptionalReferenceTypeFieldsClass dst =
			MessagePack.unpack(raw, GeneralOptionalReferenceTypeFieldsClass.class);
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
	}

	@Test
	public void testGeneralOptionalReferenceTypeFieldsClass02()
			throws Exception {
		GeneralOptionalReferenceTypeFieldsClass src = null;

		byte[] raw = MessagePack.pack(src);

		GeneralOptionalReferenceTypeFieldsClass dst =
			MessagePack.unpack(raw, GeneralOptionalReferenceTypeFieldsClass.class);
		assertEquals(src, dst);
	}

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

		byte[] raw = MessagePack.pack(src);

		SampleListTypes dst =
			MessagePack.unpack(raw, SampleListTypes.class);
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
	}

	@Test
	public void testListTypes01() throws Exception {
		SampleListTypes src = null;

		byte[] raw = MessagePack.pack(src);

		SampleListTypes dst =
			MessagePack.unpack(raw, SampleListTypes.class);
		assertEquals(src, dst);
	}

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

		byte[] raw = MessagePack.pack(src);

		SampleOptionalListTypes dst =
			MessagePack.unpack(raw, SampleOptionalListTypes.class);
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
	}

	@Test
	public void testOptionalListTypes01() throws Exception {
		SampleOptionalListTypes src = new SampleOptionalListTypes();
		src.f0 = new ArrayList<Integer>();
		src.f1 = null;
		src.f2 = new ArrayList<String>();
		src.f3 = new ArrayList<List<String>>();
		src.f4 = null;
		src.f5 = new ArrayList<ByteBuffer>();

		byte[] raw = MessagePack.pack(src);

		SampleOptionalListTypes dst =
			MessagePack.unpack(raw, SampleOptionalListTypes.class);
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
		assertEquals(src.f3.size(), dst.f3.size());
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5.size(), dst.f5.size());
	}

	@Test
	public void testOptionalListTypes02() throws Exception {
		SampleListTypes src = null;

		byte[] raw = MessagePack.pack(src);

		SampleListTypes dst =
			MessagePack.unpack(raw, SampleListTypes.class);
		assertEquals(src, dst);
	}

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

		byte[] raw = MessagePack.pack(src);

		SampleMapTypes dst =
			MessagePack.unpack(raw, SampleMapTypes.class);
		Iterator<Integer> srcf1 = src.f1.keySet().iterator();
		Iterator<Integer> dstf1 = dst.f1.keySet().iterator();
		while (srcf1.hasNext()) {
			Integer s1 = srcf1.next();
			Integer d1 = dstf1.next();
			assertEquals(s1, d1);
			assertEquals(src.f1.get(s1), dst.f1.get(d1));
		}
		assertEquals(src.f2.size(), dst.f2.size());
		Iterator<String> srcf2 = src.f2.keySet().iterator();
		Iterator<String> dstf2 = dst.f2.keySet().iterator();
		while (srcf2.hasNext()) {
			String s2 = srcf2.next();
			String d2 = dstf2.next();
			assertEquals(s2, d2);
			assertEquals(src.f2.get(s2), dst.f2.get(d2));
		}
	}

	@Test
	public void testMapTypes01() throws Exception {
		SampleMapTypes src = null;

		byte[] raw = MessagePack.pack(src);

		SampleMapTypes dst =
			MessagePack.unpack(raw, SampleMapTypes.class);
		assertEquals(src, dst);
	}

	public static class SampleMapTypes {
		public Map<Integer, Integer> f0;
		public Map<Integer, Integer> f1;
		public Map<String, Integer> f2;

		public SampleMapTypes() {
		}
	}

	@Test
	public void testOptionalMapTypes00() throws Exception {
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

		byte[] raw = MessagePack.pack(src);

		SampleOptionalMapTypes dst =
			MessagePack.unpack(raw, SampleOptionalMapTypes.class);
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1.size(), dst.f1.size());
		Iterator<Integer> srcf1 = src.f1.keySet().iterator();
		Iterator<Integer> dstf1 = dst.f1.keySet().iterator();
		while (srcf1.hasNext()) {
			Integer s1 = srcf1.next();
			Integer d1 = dstf1.next();
			assertEquals(s1, d1);
			assertEquals(src.f1.get(s1), dst.f1.get(d1));
		}
		assertEquals(src.f2.size(), dst.f2.size());
		Iterator<String> srcf2 = src.f2.keySet().iterator();
		Iterator<String> dstf2 = dst.f2.keySet().iterator();
		while (srcf2.hasNext()) {
			String s2 = srcf2.next();
			String d2 = dstf2.next();
			assertEquals(s2, d2);
			assertEquals(src.f2.get(s2), dst.f2.get(d2));
		}
	}

	@Test
	public void testOptionalMapTypes01() throws Exception {
		SampleOptionalMapTypes src = new SampleOptionalMapTypes();
		src.f0 = new HashMap<Integer, Integer>();
		src.f1 = null;
		src.f2 = new HashMap<String, Integer>();

		byte[] raw = MessagePack.pack(src);

		SampleOptionalMapTypes dst =
			MessagePack.unpack(raw, SampleOptionalMapTypes.class);
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
	}

	@Test
	public void testOptionalMapTypes02() throws Exception {
		SampleOptionalMapTypes src = null;

		byte[] raw = MessagePack.pack(src);

		SampleOptionalMapTypes dst =
			MessagePack.unpack(raw, SampleOptionalMapTypes.class);
		assertEquals(src, dst);
	}

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
		try {
			TemplateBuilder.build(FinalModifierClass.class);
			assertTrue(true);
		} catch (TemplateBuildException e) {
			fail();
		}
		assertTrue(true);
	}

	public final static class FinalModifierClass {
	}

	public abstract static class AbstractModifierClass {
	}

	@Test
	public void testInterfaceType00() throws Exception {
		try {
			TemplateBuilder.build(SampleInterface.class);
			fail();
		} catch (TemplateBuildException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testInterfaceType01() throws Exception {
		try {
			TemplateBuilder.build(SampleInterface.class);
			fail();
		} catch (TemplateBuildException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	public interface SampleInterface {
	}

	@Test
	public void testEnumTypeForOrdinal00() throws Exception {
		SampleEnumFieldClass src = new SampleEnumFieldClass();
		src.f0 = 0;
		src.f1 = SampleEnum.ONE;

		byte[] raw = MessagePack.pack(src);

		SampleEnumFieldClass dst =
			MessagePack.unpack(raw, SampleEnumFieldClass.class);
		assertTrue(src.f1 == dst.f1);
	}

	@Test
	public void testEnumTypeForOrdinal01() throws Exception {
		SampleEnumFieldClass src = null;

		byte[] raw = MessagePack.pack(src);

		SampleEnumFieldClass dst =
			MessagePack.unpack(raw, SampleEnumFieldClass.class);
		assertEquals(src, dst);
	}

	public static class SampleEnumFieldClass {
		public int f0;

		public SampleEnum f1;

		public SampleEnumFieldClass() {
		}
	}

	@MessagePackOrdinalEnum
	public enum SampleEnum {
		ONE, TWO, THREE;
	}

	@Test
	public void testOptionalEnumTypeForOrdinal00() throws Exception {
		SampleOptionalEnumFieldClass src = new SampleOptionalEnumFieldClass();
		src.f0 = 0;
		src.f1 = SampleOptionalEnum.ONE;

		byte[] raw = MessagePack.pack(src);

		SampleOptionalEnumFieldClass dst =
			MessagePack.unpack(raw, SampleOptionalEnumFieldClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
	}

	@Test
	public void testOptionalEnumTypeForOrdinal01() throws Exception {
		SampleOptionalEnumFieldClass src = new SampleOptionalEnumFieldClass();
		src.f1 = null;

		byte[] raw = MessagePack.pack(src);

		SampleOptionalEnumFieldClass dst =
			MessagePack.unpack(raw, SampleOptionalEnumFieldClass.class);
		assertTrue(src.f0 == dst.f0);
		assertEquals(src.f1, dst.f1);
	}

	@Test
	public void testOptionalEnumTypeForOrdinal02() throws Exception {
		SampleEnumFieldClass src = null;

		byte[] raw = MessagePack.pack(src);

		SampleEnumFieldClass dst =
			MessagePack.unpack(raw, SampleEnumFieldClass.class);
		assertEquals(src, dst);
	}

	public static class SampleOptionalEnumFieldClass {
		@Optional
		public int f0;

		@Optional
		public SampleOptionalEnum f1;

		public SampleOptionalEnumFieldClass() {
		}
	}

	@MessagePackOrdinalEnum
	public enum SampleOptionalEnum {
		ONE, TWO, THREE;
	}

	@Test
	public void testFieldModifiers() throws Exception {
		FieldModifiersClass src = new FieldModifiersClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;

		byte[] raw = MessagePack.pack(src);

		FieldModifiersClass dst =
			MessagePack.unpack(raw, FieldModifiersClass.class);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 != dst.f3);
		assertTrue(src.f4 != dst.f4);
	}

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
		OptionalFieldModifiersClass src = new OptionalFieldModifiersClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;

		byte[] raw = MessagePack.pack(src);

		OptionalFieldModifiersClass dst =
			MessagePack.unpack(raw, OptionalFieldModifiersClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 != dst.f3);
		assertTrue(src.f4 != dst.f4);
	}

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
		BaseClass src = new BaseClass();
		NestedClass src2 = new NestedClass();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		byte[] raw = MessagePack.pack(src);

		BaseClass dst =
			MessagePack.unpack(raw, BaseClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testNestedFieldClass01() throws Exception {
		BaseClass src = null;

		byte[] raw = MessagePack.pack(src);

		BaseClass dst =
			MessagePack.unpack(raw, BaseClass.class);
		assertEquals(src, dst);
	}

	public static class BaseClass {
		public int f0;
		public NestedClass f1;

		public BaseClass() {
		}
	}

	public static class NestedClass {
		public int f2;

		public NestedClass() {
		}
	}

	@Test
	public void testOptionalNestedFieldClass00() throws Exception {
		OptionalBaseClass src = new OptionalBaseClass();
		OptionalNestedClass src2 = new OptionalNestedClass();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseClass dst =
			MessagePack.unpack(raw, OptionalBaseClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testOptionalNestedFieldClass01() throws Exception {
		OptionalBaseClass src = new OptionalBaseClass();
		src.f1 = null;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseClass dst =
			MessagePack.unpack(raw, OptionalBaseClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
	}

	@Test
	public void testOptionalNestedFieldClass02() throws Exception {
		OptionalBaseClass src = null;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseClass dst =
			MessagePack.unpack(raw, OptionalBaseClass.class);
		assertEquals(src, dst);
	}

	public static class OptionalBaseClass {
		@Optional
		public int f0;
		@Optional
		public OptionalNestedClass f1;

		public OptionalBaseClass() {
		}
	}

	public static class OptionalNestedClass {
		@Optional
		public int f2;

		public OptionalNestedClass() {
		}
	}

	@Test
	public void testMessagePackMessageFieldClass00() throws Exception {
		BaseClass2 src = new BaseClass2();
		MessagePackMessageClass2 src2 = new MessagePackMessageClass2();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		byte[] raw = MessagePack.pack(src);

		BaseClass2 dst =
			MessagePack.unpack(raw, BaseClass2.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testMessagePackMessageFieldClass01() throws Exception {
		BaseClass2 src = null;

		byte[] raw = MessagePack.pack(src);

		BaseClass2 dst =
			MessagePack.unpack(raw, BaseClass2.class);
		assertEquals(src, dst);
	}

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
		OptionalBaseClass2 src = new OptionalBaseClass2();
		OptionalMessagePackMessageClass2 src2 = new OptionalMessagePackMessageClass2();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseClass2 dst =
			MessagePack.unpack(raw, OptionalBaseClass2.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testOptionalMessagePackMessageFieldClass01() throws Exception {
		OptionalBaseClass2 src = new OptionalBaseClass2();
		src.f1 = null;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseClass2 dst =
			MessagePack.unpack(raw, OptionalBaseClass2.class);
		assertTrue(src.f0 == dst.f0);
		assertEquals(src.f1, dst.f1);
	}

	@Test
	public void testOptionalMessagePackMessageFieldClass02() throws Exception {
		OptionalBaseClass2 src = null;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseClass2 dst =
			MessagePack.unpack(raw, OptionalBaseClass2.class);
		assertEquals(src, dst);
	}

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
		SampleSubClass src = new SampleSubClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f8 = 8;
		src.f9 = 9;

		byte[] raw = MessagePack.pack(src);

		SampleSubClass dst =
			MessagePack.unpack(raw, SampleSubClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 != dst.f3);
		assertTrue(src.f4 != dst.f4);
		assertTrue(src.f5 == dst.f5);
		assertTrue(src.f6 == dst.f6);
		assertTrue(src.f8 != dst.f8);
		assertTrue(src.f9 != dst.f9);
	}

	@Test
	public void testExtendedClass01() throws Exception {
		SampleSubClass src = null;

		byte[] raw = MessagePack.pack(src);

		SampleSubClass dst =
			MessagePack.unpack(raw, SampleSubClass.class);
		assertEquals(src, dst);
	}

	public static class SampleSubClass extends SampleSuperClass {
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public SampleSubClass() {
		}
	}

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
		SampleOptionalSubClass src = new SampleOptionalSubClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f8 = 8;
		src.f9 = 9;

		byte[] raw = MessagePack.pack(src);

		SampleOptionalSubClass dst =
			MessagePack.unpack(raw, SampleOptionalSubClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 != dst.f3);
		assertTrue(src.f4 != dst.f4);
		assertTrue(src.f5 == dst.f5);
		assertTrue(src.f6 == dst.f6);
		assertTrue(src.f8 != dst.f8);
		assertTrue(src.f9 != dst.f9);
	}

	@Test
	public void testOptionalExtendedClass01() throws Exception {
		SampleOptionalSubClass src = null;

		byte[] raw = MessagePack.pack(src);

		SampleOptionalSubClass dst =
			MessagePack.unpack(raw, SampleOptionalSubClass.class);
		assertEquals(src, dst);
	}

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

	@Test
	public void testMessagePackableUnpackableClass00() throws Exception {
		BaseMessagePackableUnpackableClass src = new BaseMessagePackableUnpackableClass();
		MessagePackableUnpackableClass src1 = new MessagePackableUnpackableClass();
		List<MessagePackableUnpackableClass> src2 = new ArrayList<MessagePackableUnpackableClass>();
		src1.f0 = 0;
		src1.f1 = 1;
		src.f0 = src1;
		src.f1 = 1;
		src2.add(src1);
		src.f2 = src2;

		byte[] raw = MessagePack.pack(src);

		BaseMessagePackableUnpackableClass dst =
			MessagePack.unpack(raw, BaseMessagePackableUnpackableClass.class);
		assertEquals(src.f0.f0, dst.f0.f0);
		assertEquals(src.f0.f1, dst.f0.f1);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
		assertEquals(src.f2.get(0).f0, dst.f2.get(0).f0);
		assertEquals(src.f2.get(0).f1, dst.f2.get(0).f1);
	}

	@Test
	public void testMessagePackableUnpackableClass01() throws Exception {
		BaseMessagePackableUnpackableClass src = null;

		byte[] raw = MessagePack.pack(src);

		BaseMessagePackableUnpackableClass dst =
			MessagePack.unpack(raw, BaseMessagePackableUnpackableClass.class);
		assertEquals(src, dst);
	}

	public static class BaseMessagePackableUnpackableClass {
		public MessagePackableUnpackableClass f0;
		public int f1;
		public List<MessagePackableUnpackableClass> f2;

		public BaseMessagePackableUnpackableClass() {
		}
	}

	public static class MessagePackableUnpackableClass implements
			MessagePackable, MessageUnpackable {
		public int f0;
		public int f1;

		public MessagePackableUnpackableClass() {
		}

		@Override
		public void messagePack(Packer packer) throws IOException {
			packer.packArray(2);
			packer.pack(f0);
			packer.pack(f1);
		}

		@Override
		public void messageUnpack(Unpacker unpacker) throws IOException,
				MessageTypeException {
			if (unpacker.tryUnpackNull()) {
				return;
			}
			unpacker.unpackArray();
			f0 = unpacker.unpackInt();
			f1 = unpacker.unpackInt();
		}
	}

	@Test
	public void testOptionalMessagePackableUnpackableClass00() throws Exception {
		OptionalBaseMessagePackableUnpackableClass src = new OptionalBaseMessagePackableUnpackableClass();
		OptionalMessagePackableUnpackableClass src1 = new OptionalMessagePackableUnpackableClass();
		List<OptionalMessagePackableUnpackableClass> src2 = new ArrayList<OptionalMessagePackableUnpackableClass>();
		src1.f0 = 0;
		src1.f1 = 1;
		src.f0 = src1;
		src.f1 = 1;
		src2.add(src1);
		src.f2 = src2;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseMessagePackableUnpackableClass dst =
			MessagePack.unpack(raw, OptionalBaseMessagePackableUnpackableClass.class);
		assertEquals(src.f0.f0, dst.f0.f0);
		assertEquals(src.f0.f1, dst.f0.f1);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
		assertEquals(src.f2.get(0).f0, dst.f2.get(0).f0);
		assertEquals(src.f2.get(0).f1, dst.f2.get(0).f1);
	}

	@Test
	public void testOptionalMessagePackableUnpackableClass01() throws Exception {
		OptionalBaseMessagePackableUnpackableClass src = new OptionalBaseMessagePackableUnpackableClass();
		src.f0 = null;
		src.f1 = 1;
		src.f2 = null;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseMessagePackableUnpackableClass dst =
			MessagePack.unpack(raw, OptionalBaseMessagePackableUnpackableClass.class);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
	}

	@Test
	public void testOptionalMessagePackableUnpackableClass02() throws Exception {
		OptionalBaseMessagePackableUnpackableClass src = null;

		byte[] raw = MessagePack.pack(src);

		OptionalBaseMessagePackableUnpackableClass dst =
			MessagePack.unpack(raw, OptionalBaseMessagePackableUnpackableClass.class);
		assertEquals(src, dst);
	}

	public static class OptionalBaseMessagePackableUnpackableClass {
		@Optional
		public OptionalMessagePackableUnpackableClass f0;
		@Optional
		public int f1;
		@Optional
		public List<OptionalMessagePackableUnpackableClass> f2;

		public OptionalBaseMessagePackableUnpackableClass() {
		}
	}

	public static class OptionalMessagePackableUnpackableClass implements
			MessagePackable, MessageUnpackable {
		@Optional
		public int f0;
		@Optional
		public int f1;

		public OptionalMessagePackableUnpackableClass() {
		}

		@Override
		public void messagePack(Packer packer) throws IOException {
			packer.packArray(2);
			packer.pack(f0);
			packer.pack(f1);
		}

		@Override
		public void messageUnpack(Unpacker unpacker) throws IOException,
				MessageTypeException {
			if (unpacker.tryUnpackNull()) {
				return;
			}
			unpacker.unpackArray();
			f0 = unpacker.unpackInt();
			f1 = unpacker.unpackInt();
		}
	}
}

