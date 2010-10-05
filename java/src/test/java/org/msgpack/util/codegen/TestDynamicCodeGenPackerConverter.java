package org.msgpack.util.codegen;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
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
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePacker;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;

public class TestDynamicCodeGenPackerConverter extends TestCase {

	@Test
	public void testPrimitiveTypeFields() throws Exception {
		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker
				.create(PrimitiveTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicCodeGenTemplate
				.create(PrimitiveTypeFieldsClass.class);
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
	public void testGeneralReferenceTypeFieldsClass() throws Exception {
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
		MessagePacker packer = DynamicCodeGenPacker
				.create(GeneralReferenceTypeFieldsClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicCodeGenTemplate
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

	public void testListTypes() throws Exception {
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
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker
				.create(SampleListTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicCodeGenTemplate.create(SampleListTypes.class);
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
		assertFalse(it.hasNext());
	}

	public static class SampleListTypes {
		public List<Integer> f0;
		public List<Integer> f1;
		public List<String> f2;

		public SampleListTypes() {
		}
	}

	public void testMapTypes() throws Exception {
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
		MessagePacker packer = DynamicCodeGenPacker
				.create(SampleMapTypes.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicCodeGenTemplate.create(SampleMapTypes.class);
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
			DynamicCodeGenPacker.create(NoDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenPacker.create(PrivateDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenPacker.create(ProtectedDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenPacker.create(PackageDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testDefaultConstructorModifiers02() throws Exception {
		try {
			DynamicCodeGenTemplate.create(NoDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenTemplate.create(PrivateDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenTemplate
					.create(ProtectedDefaultConstructorClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenTemplate.create(PackageDefaultConstructorClass.class);
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
			DynamicCodeGenPacker.create(PrivateModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenPacker.create(ProtectedModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenPacker.create(PackageModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testClassModifiers02() throws Exception {
		try {
			DynamicCodeGenTemplate.create(PrivateModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenTemplate.create(ProtectedModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenTemplate.create(PackageModifierClass.class);
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
			DynamicCodeGenPacker.create(FinalModifierClass.class);
			assertTrue(true);
		} catch (DynamicCodeGenException e) {
			fail();
		}
		assertTrue(true);
		try {
			DynamicCodeGenPacker.create(AbstractModifierClass.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testFinalClassAndAbstractClass02() throws Exception {
		try {
			DynamicCodeGenTemplate.create(FinalModifierClass.class);
			assertTrue(true);
		} catch (DynamicCodeGenException e) {
			fail();
		}
		assertTrue(true);
		try {
			DynamicCodeGenTemplate.create(AbstractModifierClass.class);
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
			DynamicCodeGenPacker.create(SampleInterface.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			DynamicCodeGenPacker.create(SampleEnum.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testInterfaceType() throws Exception {
		try {
			DynamicCodeGenTemplate.create(SampleInterface.class);
			fail();
		} catch (DynamicCodeGenException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	public interface SampleInterface {
	}

	@Test
	public void testEnumTypeForOrdinal() throws Exception {
		SampleEnumFieldClass src = new SampleEnumFieldClass();
		src.f0 = 0;
		src.f1 = SampleEnum.ONE;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker
				.create(SampleEnumFieldClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicCodeGenTemplate
				.create(SampleEnumFieldClass.class);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleEnumFieldClass dst = (SampleEnumFieldClass) tmpl.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
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
		MessagePacker packer = DynamicCodeGenPacker
				.create(FieldModifiersClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicCodeGenTemplate
				.create(FieldModifiersClass.class);
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
	public void testNestedFieldClass() throws Exception {
		MessagePacker packer2 = DynamicCodeGenPacker.create(NestedClass.class);
		CustomPacker.register(NestedClass.class, packer2);
		MessagePacker packer1 = DynamicCodeGenPacker.create(BaseClass.class);
		CustomPacker.register(BaseClass.class, packer1);
		Template tmpl2 = DynamicCodeGenTemplate.create(NestedClass.class);
		CustomUnpacker.register(NestedClass.class, tmpl2);
		CustomConverter.register(NestedClass.class, tmpl2);
		Template tmpl1 = DynamicCodeGenTemplate.create(BaseClass.class);
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
	public void testMessagePackMessageFieldClass() throws Exception {
		BaseClass2 src = new BaseClass2();
		MessagePackMessageClass2 src2 = new MessagePackMessageClass2();
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker.create(BaseClass2.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		Template tmpl = DynamicCodeGenTemplate.create(BaseClass2.class);
		BaseClass2 dst = (BaseClass2) tmpl.convert(mpo);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1.f2 == dst.f1.f2);
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
	public void testExtendedClass() throws Exception {
		SampleSubClass src = new SampleSubClass();
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f8 = 8;
		src.f9 = 9;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DynamicCodeGenPacker
				.create(SampleSubClass.class);
		packer.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DynamicCodeGenTemplate.create(SampleSubClass.class);
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
}
