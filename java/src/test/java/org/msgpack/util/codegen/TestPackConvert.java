package org.msgpack.util.codegen;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import junit.framework.TestCase;

import org.junit.Test;
import org.msgpack.CustomConverter;
import org.msgpack.CustomPacker;
import org.msgpack.CustomUnpacker;
import org.msgpack.MessageConvertable;
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePackable;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;

public class TestPackConvert extends TestCase {

	@Test
	public void testPrimitiveTypeField00s() throws Exception {
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
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl
				.convert(mpo);
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
	public void testPrimitiveTypeFields01() throws Exception {
		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(PrimitiveTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(PrimitiveTypeFieldsClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl
				.convert(mpo);
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
	public void testPrimitiveTypeFields02() throws Exception {
		PrimitiveTypeFieldsClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(PrimitiveTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(PrimitiveTypeFieldsClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) tmpl
				.convert(mpo);
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(GeneralReferenceTypeFieldsClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl
				.convert(mpo);
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
	public void XtestGeneralReferenceTypeFieldsClass01() throws Exception {
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(GeneralReferenceTypeFieldsClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl
				.convert(mpo);
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
	public void XtestGeneralReferenceTypeFieldsClass02() throws Exception {
		GeneralReferenceTypeFieldsClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(GeneralReferenceTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(GeneralReferenceTypeFieldsClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) tmpl
				.convert(mpo);
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleListTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleListTypes.class);
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
		src.f3 = null;
		src.f4 = new ArrayList<SampleListNestedType>();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleListTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleListTypes.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleListTypes dst = (SampleListTypes) tmpl.convert(mpo);
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4.size(), dst.f4.size());
		assertFalse(it.hasNext());
	}

	@Test
	public void testListTypes02() throws Exception {
		SampleListTypes src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleListTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleListTypes.class);
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleMapTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleMapTypes.class);
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleMapTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleMapTypes.class);
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleMapTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleMapTypes.class);
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

	@Test
	public void testDefaultConstructorModifiers01() throws Exception {
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
	public void testDefaultConstructorModifiers02() throws Exception {
		try {
			DynamicTemplate.create(NoDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicTemplate.create(PrivateDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicTemplate.create(ProtectedDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicTemplate.create(PackageDefaultConstructorClass.class);
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
	public void testClassModifiers01() throws Exception {
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
	public void testClassModifiers02() throws Exception {
		try {
			DynamicTemplate.create(PrivateModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicTemplate.create(ProtectedModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicTemplate.create(PackageModifierClass.class);
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
	public void testFinalClassAndAbstractClass01() throws Exception {
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
	public void testFinalClassAndAbstractClass02() throws Exception {
		try {
			DynamicTemplate.create(FinalModifierClass.class);
			assertTrue(true);
		} catch (DynamicCodeGenException e) {
			fail();
		}
		assertTrue(true);
		try {
			DynamicTemplate.create(AbstractModifierClass.class);
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
	public void testInterfaceAndEnumType01() throws Exception {
		try {
			DynamicPacker.create(SampleInterface.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicPacker.create(SampleEnum.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testInterfaceType() throws Exception {
		try {
			DynamicTemplate.create(SampleInterface.class);
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
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleEnumFieldClass dst = (SampleEnumFieldClass) tmpl.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertFalse(it.hasNext());
	}

	@Test
	public void testEnumTypeForOrdinal01() throws Exception {
		SampleEnumFieldClass src = new SampleEnumFieldClass();
		src.f1 = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleEnumFieldClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleEnumFieldClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleEnumFieldClass dst = (SampleEnumFieldClass) tmpl.convert(mpo);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertFalse(it.hasNext());
	}

	@Test
	public void testEnumTypeForOrdinal02() throws Exception {
		SampleEnumFieldClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleEnumFieldClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleEnumFieldClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleEnumFieldClass dst = (SampleEnumFieldClass) tmpl.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
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
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		FieldModifiersClass dst = (FieldModifiersClass) tmpl.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 != dst.f3);
		assertTrue(src.f4 != dst.f4);
		assertFalse(it.hasNext());
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
	public void testNestedFieldClass00() throws Exception {
		MessagePacker packer2 = DynamicPacker.create(NestedClass.class);
		CustomPacker.register(NestedClass.class, packer2);
		MessagePacker packer1 = DynamicPacker.create(BaseClass.class);
		CustomPacker.register(BaseClass.class, packer1);
		Template tmpl2 = DynamicTemplate.create(NestedClass.class);
		CustomUnpacker.register(NestedClass.class, tmpl2);
		CustomConverter.register(NestedClass.class, tmpl2);
		Template tmpl1 = DynamicTemplate.create(BaseClass.class);
		CustomUnpacker.register(BaseClass.class, tmpl1);
		CustomConverter.register(BaseClass.class, tmpl1);
		BaseClass src = new BaseClass();
		NestedClass src2 = new NestedClass();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		packer1.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		BaseClass dst = (BaseClass) tmpl1.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
		assertFalse(it.hasNext());
	}

	@Test
	public void testNestedFieldClass01() throws Exception {
		MessagePacker packer2 = DynamicPacker.create(NestedClass.class);
		CustomPacker.register(NestedClass.class, packer2);
		MessagePacker packer1 = DynamicPacker.create(BaseClass.class);
		CustomPacker.register(BaseClass.class, packer1);
		Template tmpl2 = DynamicTemplate.create(NestedClass.class);
		CustomUnpacker.register(NestedClass.class, tmpl2);
		CustomConverter.register(NestedClass.class, tmpl2);
		Template tmpl1 = DynamicTemplate.create(BaseClass.class);
		CustomUnpacker.register(BaseClass.class, tmpl1);
		CustomConverter.register(BaseClass.class, tmpl1);
		BaseClass src = new BaseClass();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		packer1.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		BaseClass dst = (BaseClass) tmpl1.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertEquals(src.f1, dst.f1);
		assertFalse(it.hasNext());
	}

	@Test
	public void testNestedFieldClass02() throws Exception {
		MessagePacker packer2 = DynamicPacker.create(NestedClass.class);
		CustomPacker.register(NestedClass.class, packer2);
		MessagePacker packer1 = DynamicPacker.create(BaseClass.class);
		CustomPacker.register(BaseClass.class, packer1);
		Template tmpl2 = DynamicTemplate.create(NestedClass.class);
		CustomUnpacker.register(NestedClass.class, tmpl2);
		CustomConverter.register(NestedClass.class, tmpl2);
		Template tmpl1 = DynamicTemplate.create(BaseClass.class);
		CustomUnpacker.register(BaseClass.class, tmpl1);
		CustomConverter.register(BaseClass.class, tmpl1);
		BaseClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		packer1.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		BaseClass dst = (BaseClass) tmpl1.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
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
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		Template tmpl = DynamicTemplate.create(BaseClass2.class);
		BaseClass2 dst = (BaseClass2) tmpl.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
		assertFalse(it.hasNext());
	}

	@Test
	public void testMessagePackMessageFieldClass01() throws Exception {
		BaseClass2 src = new BaseClass2();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(BaseClass2.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		Template tmpl = DynamicTemplate.create(BaseClass2.class);
		BaseClass2 dst = (BaseClass2) tmpl.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertEquals(src.f1, dst.f1);
		assertFalse(it.hasNext());
	}

	@Test
	public void testMessagePackMessageFieldClass02() throws Exception {
		BaseClass2 src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(BaseClass2.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		Template tmpl = DynamicTemplate.create(BaseClass2.class);
		BaseClass2 dst = (BaseClass2) tmpl.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
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
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleSubClass dst = (SampleSubClass) tmpl.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 != dst.f3);
		assertTrue(src.f4 != dst.f4);
		assertTrue(src.f5 == dst.f5);
		assertTrue(src.f6 == dst.f6);
		assertTrue(src.f8 != dst.f8);
		assertTrue(src.f9 != dst.f9);
		assertFalse(it.hasNext());
	}

	@Test
	public void testExtendedClass01() throws Exception {
		SampleSubClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker.create(SampleSubClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate.create(SampleSubClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleSubClass dst = (SampleSubClass) tmpl.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
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
	public void testMessagePackableUnpackableClass00() throws Exception {
		BaseMessagePackableConvertableClass src = new BaseMessagePackableConvertableClass();
		MessagePackableConvertableClass src1 = new MessagePackableConvertableClass();
		List<MessagePackableConvertableClass> src2 = new ArrayList<MessagePackableConvertableClass>();
		src1.f0 = 0;
		src1.f1 = 1;
		src.f0 = src1;
		src.f1 = 1;
		src2.add(src1);
		src.f2 = src2;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(BaseMessagePackableConvertableClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(BaseMessagePackableConvertableClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		BaseMessagePackableConvertableClass dst = (BaseMessagePackableConvertableClass) tmpl
				.convert(mpo);
		assertEquals(src.f0.f0, dst.f0.f0);
		assertEquals(src.f0.f1, dst.f0.f1);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2.size(), dst.f2.size());
		assertEquals(src.f2.get(0).f0, dst.f2.get(0).f0);
		assertEquals(src.f2.get(0).f1, dst.f2.get(0).f1);
		assertFalse(it.hasNext());
	}

	@Test
	public void testMessagePackableUnpackableClass01() throws Exception {
		BaseMessagePackableConvertableClass src = new BaseMessagePackableConvertableClass();
		src.f0 = null;
		src.f1 = 1;
		src.f2 = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(BaseMessagePackableConvertableClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(BaseMessagePackableConvertableClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		BaseMessagePackableConvertableClass dst = (BaseMessagePackableConvertableClass) tmpl
				.convert(mpo);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertFalse(it.hasNext());
	}

	@Test
	public void testMessagePackableUnpackableClass02() throws Exception {
		BaseMessagePackableConvertableClass src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicPacker
				.create(BaseMessagePackableConvertableClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicTemplate
				.create(BaseMessagePackableConvertableClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		BaseMessagePackableConvertableClass dst = (BaseMessagePackableConvertableClass) tmpl
				.convert(mpo);
		assertEquals(src, dst);
		assertFalse(it.hasNext());
	}

	public static class BaseMessagePackableConvertableClass {
		public MessagePackableConvertableClass f0;

		public int f1;

		public List<MessagePackableConvertableClass> f2;

		public BaseMessagePackableConvertableClass() {
		}
	}

	public static class MessagePackableConvertableClass implements
			MessagePackable, MessageConvertable {

		public int f0;

		public int f1;

		public MessagePackableConvertableClass() {
		}

		@Override
		public void messagePack(Packer packer) throws IOException {
			packer.packArray(2);
			packer.pack(f0);
			packer.pack(f1);
		}

		@Override
		public void messageConvert(MessagePackObject from)
				throws MessageTypeException {
			if (from.isNil()) {
				return;
			}
			MessagePackObject[] objs = from.asArray();
			f0 = objs[0].asInt();
			f1 = objs[1].asInt();
		}
	}
}
