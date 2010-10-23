package org.msgpack.util.codegen;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.junit.Test;
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePacker;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.packer.OptionalPacker;
import org.msgpack.template.ListTemplate;
import org.msgpack.template.MapTemplate;
import org.msgpack.template.OptionalTemplate;
import static org.msgpack.Templates.tBigInteger;
import static org.msgpack.Templates.tBoolean;
import static org.msgpack.Templates.tByte;
import static org.msgpack.Templates.tByteArray;
import static org.msgpack.Templates.tDouble;
import static org.msgpack.Templates.tFloat;
import static org.msgpack.Templates.tInteger;
import static org.msgpack.Templates.tLong;
import static org.msgpack.Templates.tShort;
import static org.msgpack.Templates.tString;

import junit.framework.TestCase;

public class TestPackConvertWithFieldOption extends TestCase {

	@Test
	public void testPrimitiveTypeFieldsClass00() throws Exception {
		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", tByte()));
		opts.add(new FieldOption("f1", tShort()));
		opts.add(new FieldOption("f2", tInteger()));
		opts.add(new FieldOption("f3", tLong()));
		opts.add(new FieldOption("f4", tFloat()));
		opts.add(new FieldOption("f5", tDouble()));
		opts.add(new FieldOption("f6", tBoolean()));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(
				PrimitiveTypeFieldsClass.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(PrimitiveTypeFieldsClass.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl.convert(mpo);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5, dst.f5);
		assertEquals(src.f6, dst.f6);
		assertFalse(it.hasNext());
	}

	@Test
	public void testPrimitiveTypeFieldsClass01() throws Exception {
		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new OptionalTemplate(tByte())));
		opts.add(new FieldOption("f1", new OptionalTemplate(tShort())));
		opts.add(new FieldOption("f2", new OptionalTemplate(tInteger())));
		opts.add(new FieldOption("f3", new OptionalTemplate(tLong())));
		opts.add(new FieldOption("f4", new OptionalTemplate(tFloat())));
		opts.add(new FieldOption("f5", new OptionalTemplate(tDouble())));
		opts.add(new FieldOption("f6", new OptionalTemplate(tBoolean())));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(
				PrimitiveTypeFieldsClass.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(PrimitiveTypeFieldsClass.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl.convert(mpo);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5, dst.f5);
		assertEquals(src.f6, dst.f6);
		assertFalse(it.hasNext());
	}

	@Test
	public void testPrimitiveTypeFieldsClass02() throws Exception {
		PrimitiveTypeFieldsClass src = null;

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", tByte()));
		opts.add(new FieldOption("f1", tShort()));
		opts.add(new FieldOption("f2", tInteger()));
		opts.add(new FieldOption("f3", tLong()));
		opts.add(new FieldOption("f4", tFloat()));
		opts.add(new FieldOption("f5", tDouble()));
		opts.add(new FieldOption("f6", tBoolean()));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker.create(
				PrimitiveTypeFieldsClass.class, opts));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate.create(PrimitiveTypeFieldsClass.class, opts));
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
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

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", tByte()));
		opts.add(new FieldOption("f1", tShort()));
		opts.add(new FieldOption("f2", tInteger()));
		opts.add(new FieldOption("f3", tLong()));
		opts.add(new FieldOption("f4", tFloat()));
		opts.add(new FieldOption("f5", tDouble()));
		opts.add(new FieldOption("f6", tBoolean()));
		opts.add(new FieldOption("f7", tBigInteger()));
		opts.add(new FieldOption("f8", tString()));
		opts.add(new FieldOption("f9", tByteArray()));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(GeneralReferenceTypeFieldsClass.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl.convert(mpo);
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
		assertFalse(it.hasNext());
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass01() throws Exception {
		GeneralReferenceTypeFieldsClass src = new GeneralReferenceTypeFieldsClass();
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

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new OptionalTemplate(tByte())));
		opts.add(new FieldOption("f1", new OptionalTemplate(tShort())));
		opts.add(new FieldOption("f2", new OptionalTemplate(tInteger())));
		opts.add(new FieldOption("f3", new OptionalTemplate(tLong())));
		opts.add(new FieldOption("f4", new OptionalTemplate(tFloat())));
		opts.add(new FieldOption("f5", new OptionalTemplate(tDouble())));
		opts.add(new FieldOption("f6", new OptionalTemplate(tBoolean())));
		opts.add(new FieldOption("f7", new OptionalTemplate(tBigInteger())));
		opts.add(new FieldOption("f8", new OptionalTemplate(tString())));
		opts.add(new FieldOption("f9", new OptionalTemplate(tByteArray())));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(GeneralReferenceTypeFieldsClass.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl.convert(mpo);
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
		assertFalse(it.hasNext());
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass02()
			throws Exception {
		GeneralReferenceTypeFieldsClass src = null;

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new OptionalTemplate(tByte())));
		opts.add(new FieldOption("f1", new OptionalTemplate(tShort())));
		opts.add(new FieldOption("f2", new OptionalTemplate(tInteger())));
		opts.add(new FieldOption("f3", new OptionalTemplate(tLong())));
		opts.add(new FieldOption("f4", new OptionalTemplate(tFloat())));
		opts.add(new FieldOption("f5", new OptionalTemplate(tDouble())));
		opts.add(new FieldOption("f6", new OptionalTemplate(tBoolean())));
		opts.add(new FieldOption("f7", new OptionalTemplate(tBigInteger())));
		opts.add(new FieldOption("f8", new OptionalTemplate(tString())));
		opts.add(new FieldOption("f9", new OptionalTemplate(tByteArray())));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class, opts));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(GeneralReferenceTypeFieldsClass.class, opts));
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
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

		public GeneralReferenceTypeFieldsClass() {
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

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new ListTemplate(tInteger())));
		opts.add(new FieldOption("f1", new ListTemplate(tInteger())));
		opts.add(new FieldOption("f2", new ListTemplate(tString())));
		opts.add(new FieldOption("f3", new ListTemplate(new ListTemplate(tString()))));
		opts.add(new FieldOption("f4", new ListTemplate(DynamicTemplate.create(SampleListNestedType.class))));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleListTypes.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleListTypes.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleListTypes dst = (SampleListTypes) tmpl.convert(mpo);
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
		assertFalse(it.hasNext());
	}

	@Test
	public void testListTypes01() throws Exception {
		SampleListTypes src = new SampleListTypes();
		src.f0 = new ArrayList<Integer>();
		src.f1 = null;
		src.f2 = new ArrayList<String>();
		src.f3 = new ArrayList<List<String>>();
		src.f4 = null;

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new OptionalTemplate(new ListTemplate(tInteger()))));
		opts.add(new FieldOption("f1", new OptionalTemplate(new ListTemplate(tInteger()))));
		opts.add(new FieldOption("f2", new OptionalTemplate(new ListTemplate(tString()))));
		opts.add(new FieldOption("f3", new OptionalTemplate(new ListTemplate(new ListTemplate(tString())))));
		opts.add(new FieldOption("f4", new OptionalTemplate(new ListTemplate(DynamicTemplate.create(SampleListNestedType.class)))));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleListTypes.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleListTypes.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleListTypes dst = (SampleListTypes) tmpl.convert(mpo);
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
		assertEquals(src.f3.size(), dst.f3.size());
		assertEquals(src.f4, dst.f4);
		assertFalse(it.hasNext());
	}

	@Test
	public void testListTypes02() throws Exception {
		SampleListTypes src = null;

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new OptionalTemplate(new ListTemplate(tInteger()))));
		opts.add(new FieldOption("f1", new OptionalTemplate(new ListTemplate(tInteger()))));
		opts.add(new FieldOption("f2", new OptionalTemplate(new ListTemplate(tString()))));
		opts.add(new FieldOption("f3", new OptionalTemplate(new ListTemplate(new ListTemplate(tString())))));
		opts.add(new FieldOption("f4", new OptionalTemplate(new ListTemplate(DynamicTemplate.create(SampleListNestedType.class)))));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleListTypes.class));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate
				.create(SampleListTypes.class, opts));
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleListTypes dst = (SampleListTypes) tmpl.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
	}

	public static class SampleListTypes {
		public List<Integer> f0;
		public List<Integer> f1;
		public List<String> f2;
		public List<List<String>> f3;
		public List<SampleListNestedType> f4;

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

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new MapTemplate(tInteger(), tInteger())));
		opts.add(new FieldOption("f1", new MapTemplate(tInteger(), tInteger())));
		opts.add(new FieldOption("f2", new MapTemplate(tString(), tInteger())));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleMapTypes.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleMapTypes.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleMapTypes dst = (SampleMapTypes) tmpl.convert(mpo);
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
		assertFalse(it.hasNext());
	}

	@Test
	public void testMapTypes01() throws Exception {
		SampleMapTypes src = new SampleMapTypes();
		src.f0 = new HashMap<Integer, Integer>();
		src.f1 = null;
		src.f2 = new HashMap<String, Integer>();

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new OptionalTemplate(new MapTemplate(tInteger(), tInteger()))));
		opts.add(new FieldOption("f1", new OptionalTemplate(new MapTemplate(tInteger(), tInteger()))));
		opts.add(new FieldOption("f2", new OptionalTemplate(new MapTemplate(tString(), tInteger()))));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(SampleMapTypes.class, opts);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleMapTypes.class, opts);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleMapTypes dst = (SampleMapTypes) tmpl.convert(mpo);
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
		assertFalse(it.hasNext());
	}

	@Test
	public void testMapTypes02() throws Exception {
		SampleMapTypes src = null;

		List<FieldOption> opts = new ArrayList<FieldOption>();
		opts.add(new FieldOption("f0", new OptionalTemplate(new MapTemplate(tInteger(), tInteger()))));
		opts.add(new FieldOption("f1", new OptionalTemplate(new MapTemplate(tInteger(), tInteger()))));
		opts.add(new FieldOption("f2", new OptionalTemplate(new MapTemplate(tString(), tInteger()))));
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DynamicPacker
				.create(SampleMapTypes.class, opts));
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = new OptionalTemplate(DynamicTemplate.create(SampleMapTypes.class, opts));
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleMapTypes dst = (SampleMapTypes) tmpl.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
	}

	public static class SampleMapTypes {
		public Map<Integer, Integer> f0;
		public Map<Integer, Integer> f1;
		public Map<String, Integer> f2;

		public SampleMapTypes() {
		}
	}
}
