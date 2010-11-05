package org.msgpack.util.codegen;

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
import org.msgpack.CustomMessage;
import org.msgpack.MessagePackable;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOptional;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.msgpack.packer.OptionalPacker;
import org.msgpack.template.OptionalTemplate;

import junit.framework.TestCase;

public class TestPackUnpack extends TestCase {

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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(PrimitiveTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(PrimitiveTypeFieldsClass.class);
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(PrimitiveTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(PrimitiveTypeFieldsClass.class);
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(PrimitiveTypeFieldsClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(PrimitiveTypeFieldsClass.class));
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(OptionalPrimitiveTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(OptionalPrimitiveTypeFieldsClass.class);
		OptionalPrimitiveTypeFieldsClass dst = (OptionalPrimitiveTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(OptionalPrimitiveTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(OptionalPrimitiveTypeFieldsClass.class);
		OptionalPrimitiveTypeFieldsClass dst = (OptionalPrimitiveTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(OptionalPrimitiveTypeFieldsClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(OptionalPrimitiveTypeFieldsClass.class));
		OptionalPrimitiveTypeFieldsClass dst = (OptionalPrimitiveTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class OptionalPrimitiveTypeFieldsClass {
		@MessagePackOptional
		public byte f0;
		@MessagePackOptional
		public short f1;
		@MessagePackOptional
		public int f2;
		@MessagePackOptional
		public long f3;
		@MessagePackOptional
		public float f4;
		@MessagePackOptional
		public double f5;
		@MessagePackOptional
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(GeneralReferenceTypeFieldsClass.class);
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(GeneralReferenceTypeFieldsClass.class));
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralOptionalReferenceTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(GeneralOptionalReferenceTypeFieldsClass.class);
		GeneralOptionalReferenceTypeFieldsClass dst = (GeneralOptionalReferenceTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralOptionalReferenceTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(GeneralOptionalReferenceTypeFieldsClass.class);
		GeneralOptionalReferenceTypeFieldsClass dst = (GeneralOptionalReferenceTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(GeneralOptionalReferenceTypeFieldsClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(GeneralOptionalReferenceTypeFieldsClass.class));
		GeneralOptionalReferenceTypeFieldsClass dst = (GeneralOptionalReferenceTypeFieldsClass) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class GeneralOptionalReferenceTypeFieldsClass {
		@MessagePackOptional
		public Byte f0;
		@MessagePackOptional
		public Short f1;
		@MessagePackOptional
		public Integer f2;
		@MessagePackOptional
		public Long f3;
		@MessagePackOptional
		public Float f4;
		@MessagePackOptional
		public Double f5;
		@MessagePackOptional
		public Boolean f6;
		@MessagePackOptional
		public BigInteger f7;
		@MessagePackOptional
		public String f8;
		@MessagePackOptional
		public byte[] f9;
		@MessagePackOptional
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleListTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleListTypes.class);
		SampleListTypes dst = (SampleListTypes) tmpl.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleListTypes.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleListTypes.class));
		SampleListTypes dst = (SampleListTypes) tmpl.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleOptionalListTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleOptionalListTypes.class);
		SampleOptionalListTypes dst = (SampleOptionalListTypes) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleOptionalListTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleOptionalListTypes.class);
		SampleOptionalListTypes dst = (SampleOptionalListTypes) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleOptionalListTypes.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleOptionalListTypes.class));
		SampleListTypes dst = (SampleListTypes) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class SampleOptionalListTypes {
		@MessagePackOptional
		public List<Integer> f0;
		@MessagePackOptional
		public List<Integer> f1;
		@MessagePackOptional
		public List<String> f2;
		@MessagePackOptional
		public List<List<String>> f3;
		@MessagePackOptional
		public List<SampleOptionalListNestedType> f4;
		@MessagePackOptional
		public List<ByteBuffer> f5;

		public SampleOptionalListTypes() {
		}
	}

	@MessagePackMessage
	public static class SampleOptionalListNestedType {
		@MessagePackOptional
		public byte[] f0;
		@MessagePackOptional
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleMapTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleMapTypes.class);
		SampleMapTypes dst = (SampleMapTypes) tmpl.unpack(new Unpacker(in));
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
	public void testMapTypes01() throws Exception {
		SampleMapTypes src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleMapTypes.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleMapTypes.class));
		SampleMapTypes dst = (SampleMapTypes) tmpl.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleOptionalMapTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleOptionalMapTypes.class);
		SampleOptionalMapTypes dst = (SampleOptionalMapTypes) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleOptionalMapTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleOptionalMapTypes.class);
		SampleOptionalMapTypes dst = (SampleOptionalMapTypes) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
	}

	@Test
	public void testOptionalMapTypes02() throws Exception {
		SampleOptionalMapTypes src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleOptionalMapTypes.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleOptionalMapTypes.class));
		SampleOptionalMapTypes dst = (SampleOptionalMapTypes) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class SampleOptionalMapTypes {
		@MessagePackOptional
		public Map<Integer, Integer> f0;
		@MessagePackOptional
		public Map<Integer, Integer> f1;
		@MessagePackOptional
		public Map<String, Integer> f2;

		public SampleOptionalMapTypes() {
		}
	}

	@Test
	public void testDefaultConstructorModifiers00() throws Exception {
		try {
			DynamicPacker.create(NoDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicPacker.create(PrivateDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicPacker.create(ProtectedDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicPacker.create(PackageDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testDefaultConstructorModifiers01() throws Exception {
		try {
			DynamicUnpacker.create(NoDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicUnpacker.create(PrivateDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicUnpacker.create(ProtectedDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicUnpacker.create(PackageDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	public static class NoDefaultConstructorClass {
		public NoDefaultConstructorClass(int i) {
		}
	}

	public static class PrivateDefaultConstructorClass {
		private PrivateDefaultConstructorClass() {
		}
	}

	public static class ProtectedDefaultConstructorClass {
		protected ProtectedDefaultConstructorClass() {
		}
	}

	public static class PackageDefaultConstructorClass {
		PackageDefaultConstructorClass() {
		}
	}

	@Test
	public void testClassModifiers00() throws Exception {
		try {
			DynamicPacker.create(PrivateModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicPacker.create(ProtectedModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicPacker.create(PackageModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testClassModifiers01() throws Exception {
		try {
			DynamicUnpacker.create(PrivateModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicUnpacker.create(ProtectedModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicUnpacker.create(PackageModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	private static class PrivateModifierClass {
	}

	protected static class ProtectedModifierClass {
		protected ProtectedModifierClass() {
		}
	}

	static class PackageModifierClass {
	}

	@Test
	public void testFinalClassAndAbstractClass00() throws Exception {
		try {
			DynamicPacker.create(FinalModifierClass.class);
			assertTrue(true);
		} catch (DynamicCodeGenException e) {
			fail();
		}
		assertTrue(true);
		try {
			DynamicPacker.create(AbstractModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testFinalClassAndAbstractClass01() throws Exception {
		try {
			DynamicUnpacker.create(FinalModifierClass.class);
			assertTrue(true);
		} catch (DynamicCodeGenException e) {
			fail();
		}
		assertTrue(true);
		try {
			DynamicUnpacker.create(AbstractModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
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
			DynamicPacker.create(SampleInterface.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testInterfaceType01() throws Exception {
		try {
			DynamicUnpacker.create(SampleInterface.class);
			fail();
		} catch (DynamicCodeGenException e) {
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleEnumFieldClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleEnumFieldClass.class);
		SampleEnumFieldClass dst = (SampleEnumFieldClass) tmpl
				.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
	}

	@Test
	public void testEnumTypeForOrdinal01() throws Exception {
		SampleEnumFieldClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleEnumFieldClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleEnumFieldClass.class));
		SampleEnumFieldClass dst = (SampleEnumFieldClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleOptionalEnumFieldClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(SampleOptionalEnumFieldClass.class);
		SampleOptionalEnumFieldClass dst = (SampleOptionalEnumFieldClass) tmpl
				.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
	}

	@Test
	public void testOptionalEnumTypeForOrdinal01() throws Exception {
		SampleOptionalEnumFieldClass src = new SampleOptionalEnumFieldClass();
		src.f1 = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleOptionalEnumFieldClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(SampleOptionalEnumFieldClass.class);
		SampleOptionalEnumFieldClass dst = (SampleOptionalEnumFieldClass) tmpl
				.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertEquals(src.f1, dst.f1);
	}

	@Test
	public void testOptionalEnumTypeForOrdinal02() throws Exception {
		SampleEnumFieldClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleEnumFieldClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleEnumFieldClass.class));
		SampleEnumFieldClass dst = (SampleEnumFieldClass) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class SampleOptionalEnumFieldClass {
		@MessagePackOptional
		public int f0;

		@MessagePackOptional
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(FieldModifiersClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(FieldModifiersClass.class);
		FieldModifiersClass dst = (FieldModifiersClass) tmpl
				.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(OptionalFieldModifiersClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(OptionalFieldModifiersClass.class);
		OptionalFieldModifiersClass dst = (OptionalFieldModifiersClass) tmpl
				.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 != dst.f3);
		assertTrue(src.f4 != dst.f4);
	}

	public static class OptionalFieldModifiersClass {
		@MessagePackOptional
		public int f0;
		@MessagePackOptional
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public OptionalFieldModifiersClass() {
		}
	}

	@Test
	public void testNestedFieldClass00() throws Exception {
		Template tmpl2 = DynamicTemplate.create(NestedClass.class);
		CustomMessage.register(NestedClass.class, tmpl2);
		Template tmpl = DynamicTemplate.create(BaseClass.class);
		CustomMessage.register(BaseClass.class, tmpl);
		BaseClass src = new BaseClass();
		NestedClass src2 = new NestedClass();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		BaseClass dst = (BaseClass) tmpl.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testNestedFieldClass01() throws Exception {
		Template tmpl2 = DynamicTemplate.create(NestedClass.class);
		CustomMessage.register(NestedClass.class, tmpl2);
		Template tmpl = new OptionalTemplate(DynamicTemplate.create(BaseClass.class));
		BaseClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		BaseClass dst = (BaseClass) tmpl.unpack(new Unpacker(in));
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
		Template tmpl2 = DynamicTemplate.create(OptionalNestedClass.class);
		CustomMessage.register(OptionalNestedClass.class, tmpl2);
		Template tmpl = DynamicTemplate.create(OptionalBaseClass.class);
		OptionalBaseClass src = new OptionalBaseClass();
		OptionalNestedClass src2 = new OptionalNestedClass();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		OptionalBaseClass dst = (OptionalBaseClass) tmpl.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testOptionalNestedFieldClass01() throws Exception {
		Template tmpl2 = DynamicTemplate.create(OptionalNestedClass.class);
		CustomMessage.register(OptionalNestedClass.class, tmpl2);
		Template tmpl = DynamicTemplate.create(OptionalBaseClass.class);
		CustomMessage.register(OptionalBaseClass.class, tmpl);
		OptionalBaseClass src = new OptionalBaseClass();
		src.f1 = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		OptionalBaseClass dst = (OptionalBaseClass) tmpl.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
	}

	@Test
	public void testOptionalNestedFieldClass02() throws Exception {
		Template tmpl2 = DynamicTemplate.create(OptionalNestedClass.class);
		CustomMessage.register(OptionalNestedClass.class, tmpl2);
		Template tmpl = new OptionalTemplate(DynamicTemplate.create(OptionalBaseClass.class));
		CustomMessage.register(OptionalBaseClass.class, tmpl);
		OptionalBaseClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		OptionalBaseClass dst = (OptionalBaseClass) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class OptionalBaseClass {
		@MessagePackOptional
		public int f0;
		@MessagePackOptional
		public OptionalNestedClass f1;

		public OptionalBaseClass() {
		}
	}

	public static class OptionalNestedClass {
		@MessagePackOptional
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(BaseClass2.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(BaseClass2.class);
		BaseClass2 dst = (BaseClass2) tmpl.unpack(new Unpacker(in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testMessagePackMessageFieldClass01() throws Exception {
		BaseClass2 src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(BaseClass2.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(BaseClass2.class));
		BaseClass2 dst = (BaseClass2) tmpl.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(OptionalBaseClass2.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(OptionalBaseClass2.class);
		OptionalBaseClass2 dst = (OptionalBaseClass2) tmpl.unpack(new Unpacker(
				in));
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
	}

	@Test
	public void testOptionalMessagePackMessageFieldClass01() throws Exception {
		OptionalBaseClass2 src = new OptionalBaseClass2();
		src.f1 = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(OptionalBaseClass2.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(OptionalBaseClass2.class);
		OptionalBaseClass2 dst = (OptionalBaseClass2) tmpl.unpack(new Unpacker(
				in));
		assertTrue(src.f0 == dst.f0);
		assertEquals(src.f1, dst.f1);
	}

	@Test
	public void testOptionalMessagePackMessageFieldClass02() throws Exception {
		OptionalBaseClass2 src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(OptionalBaseClass2.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(OptionalBaseClass2.class));
		OptionalBaseClass2 dst = (OptionalBaseClass2) tmpl.unpack(new Unpacker(
				in));
		assertEquals(src, dst);
	}

	public static class OptionalBaseClass2 {
		@MessagePackOptional
		public int f0;
		@MessagePackOptional
		public OptionalMessagePackMessageClass2 f1;

		public OptionalBaseClass2() {
		}
	}

	@MessagePackMessage
	public static class OptionalMessagePackMessageClass2 {
		@MessagePackOptional
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleSubClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleSubClass.class);
		SampleSubClass dst = (SampleSubClass) tmpl.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleSubClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleSubClass.class));
		SampleSubClass dst = (SampleSubClass) tmpl.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleOptionalSubClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleOptionalSubClass.class);
		SampleOptionalSubClass dst = (SampleOptionalSubClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleOptionalSubClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleOptionalSubClass.class));
		SampleOptionalSubClass dst = (SampleOptionalSubClass) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class SampleOptionalSubClass extends SampleOptionalSuperClass {
		@MessagePackOptional
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public SampleOptionalSubClass() {
		}
	}

	public static class SampleOptionalSuperClass {
		@MessagePackOptional
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(BaseMessagePackableUnpackableClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(BaseMessagePackableUnpackableClass.class);
		BaseMessagePackableUnpackableClass dst = (BaseMessagePackableUnpackableClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(BaseMessagePackableUnpackableClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(BaseMessagePackableUnpackableClass.class));
		BaseMessagePackableUnpackableClass dst = (BaseMessagePackableUnpackableClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(OptionalBaseMessagePackableUnpackableClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(OptionalBaseMessagePackableUnpackableClass.class);
		OptionalBaseMessagePackableUnpackableClass dst = (OptionalBaseMessagePackableUnpackableClass) tmpl
				.unpack(new Unpacker(in));
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(OptionalBaseMessagePackableUnpackableClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(OptionalBaseMessagePackableUnpackableClass.class);
		OptionalBaseMessagePackableUnpackableClass dst = (OptionalBaseMessagePackableUnpackableClass) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
	}

	@Test
	public void testOptionalMessagePackableUnpackableClass02() throws Exception {
		OptionalBaseMessagePackableUnpackableClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(OptionalBaseMessagePackableUnpackableClass.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(OptionalBaseMessagePackableUnpackableClass.class));
		OptionalBaseMessagePackableUnpackableClass dst = (OptionalBaseMessagePackableUnpackableClass) tmpl
				.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	public static class OptionalBaseMessagePackableUnpackableClass {
		@MessagePackOptional
		public OptionalMessagePackableUnpackableClass f0;
		@MessagePackOptional
		public int f1;
		@MessagePackOptional
		public List<OptionalMessagePackableUnpackableClass> f2;

		public OptionalBaseMessagePackableUnpackableClass() {
		}
	}

	public static class OptionalMessagePackableUnpackableClass implements
			MessagePackable, MessageUnpackable {
		@MessagePackOptional
		public int f0;
		@MessagePackOptional
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
