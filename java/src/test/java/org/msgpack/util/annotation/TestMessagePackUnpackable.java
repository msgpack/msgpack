package org.msgpack.util.annotation;

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
import org.msgpack.MessagePackObject;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class TestMessagePackUnpackable extends TestCase {

	@Test
	public void testPrimitiveTypeFields01() throws Exception {
		PrimitiveTypeFieldsClass src = (PrimitiveTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(PrimitiveTypeFieldsClass.class);
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(PrimitiveTypeFieldsClass.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
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
		PrimitiveTypeFieldsClass src = (PrimitiveTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(PrimitiveTypeFieldsClass.class);
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		PrimitiveTypeFieldsClass dst = (PrimitiveTypeFieldsClass) PackUnpackUtil
				.initEnhancedInstance(mpo, PrimitiveTypeFieldsClass.class);
		assertEquals(src.f0, dst.f0);
		assertEquals(src.f1, dst.f1);
		assertEquals(src.f2, dst.f2);
		assertEquals(src.f3, dst.f3);
		assertEquals(src.f4, dst.f4);
		assertEquals(src.f5, dst.f5);
		assertEquals(src.f6, dst.f6);
		assertFalse(it.hasNext());
	}

	@MessagePackUnpackable
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
	public void testGeneralReferenceTypeFieldsClass01() throws Exception {
		GeneralReferenceTypeFieldsClass src = (GeneralReferenceTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(GeneralReferenceTypeFieldsClass.class);
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
		new Packer(out).pack(src);
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(GeneralReferenceTypeFieldsClass.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
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
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass02() throws Exception {
		GeneralReferenceTypeFieldsClass src = (GeneralReferenceTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(GeneralReferenceTypeFieldsClass.class);
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
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		GeneralReferenceTypeFieldsClass dst = (GeneralReferenceTypeFieldsClass) PackUnpackUtil
				.initEnhancedInstance(mpo,
						GeneralReferenceTypeFieldsClass.class);
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

	@MessagePackUnpackable
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

	public void testListTypes01() throws Exception {
		SampleListTypes src = (SampleListTypes) PackUnpackUtil
				.newEnhancedInstance(SampleListTypes.class);
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
		new Packer(out).pack(src);
		SampleListTypes dst = (SampleListTypes) PackUnpackUtil
				.newEnhancedInstance(SampleListTypes.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
		assertEquals(src.f0.size(), dst.f0.size());
		assertEquals(src.f1.size(), dst.f1.size());
		for (int i = 0; i < src.f1.size(); ++i) {
			assertEquals(src.f1.get(i), dst.f1.get(i));
		}
		assertEquals(src.f2.size(), dst.f2.size());
		for (int i = 0; i < src.f2.size(); ++i) {
			assertEquals(src.f2.get(i), dst.f2.get(i));
		}
	}
	
	public void testListTypes02() throws Exception {
		SampleListTypes src = (SampleListTypes) PackUnpackUtil
				.newEnhancedInstance(SampleListTypes.class);
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
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleListTypes dst = (SampleListTypes) PackUnpackUtil
				.initEnhancedInstance(mpo, SampleListTypes.class);
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

	@MessagePackUnpackable
	public static class SampleListTypes {
		public List<Integer> f0;
		public List<Integer> f1;
		public List<String> f2;

		public SampleListTypes() {
		}
	}

	public void testMapTypes01() throws Exception {
		SampleMapTypes src = (SampleMapTypes) PackUnpackUtil
				.newEnhancedInstance(SampleMapTypes.class);
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
		new Packer(out).pack(src);
		SampleMapTypes dst = (SampleMapTypes) PackUnpackUtil
				.newEnhancedInstance(SampleMapTypes.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
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
	
	public void testMapTypes02() throws Exception {
		SampleMapTypes src = (SampleMapTypes) PackUnpackUtil
				.newEnhancedInstance(SampleMapTypes.class);
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
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleMapTypes dst = (SampleMapTypes) PackUnpackUtil
				.initEnhancedInstance(mpo, SampleMapTypes.class);
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

	@MessagePackUnpackable
	public static class SampleMapTypes {
		public Map<Integer, Integer> f0;
		public Map<Integer, Integer> f1;
		public Map<String, Integer> f2;

		public SampleMapTypes() {
		}
	}

	@Test
	public void testDefaultConstructorModifiers() throws Exception {
		try {
			PackUnpackUtil.newEnhancedInstance(NoDefaultConstructorClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			PackUnpackUtil
					.newEnhancedInstance(PrivateDefaultConstructorClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			PackUnpackUtil
					.newEnhancedInstance(ProtectedDefaultConstructorClass.class);
			assertTrue(true);
		} catch (PackUnpackUtilException e) {
			fail();
		}
		assertTrue(true);
		try {
			PackUnpackUtil
					.newEnhancedInstance(PackageDefaultConstructorClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@MessagePackUnpackable
	public static class NoDefaultConstructorClass {
		public NoDefaultConstructorClass(int i) {
		}
	}

	@MessagePackUnpackable
	public static class PrivateDefaultConstructorClass {
		private PrivateDefaultConstructorClass() {
		}
	}

	@MessagePackUnpackable
	public static class ProtectedDefaultConstructorClass {
		protected ProtectedDefaultConstructorClass() {
		}
	}

	@MessagePackUnpackable
	public static class PackageDefaultConstructorClass {
		PackageDefaultConstructorClass() {
		}
	}

	@Test
	public void testClassModifiers() throws Exception {
		try {
			PackUnpackUtil.newEnhancedInstance(PrivateModifierClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			PackUnpackUtil.newEnhancedInstance(ProtectedModifierClass.class);
			assertTrue(true);
		} catch (PackUnpackUtilException e) {
			fail();
		}
		assertTrue(true);
		try {
			PackUnpackUtil.newEnhancedInstance(PackageModifierClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@MessagePackUnpackable
	private static class PrivateModifierClass {
	}

	@MessagePackUnpackable
	protected static class ProtectedModifierClass {
		protected ProtectedModifierClass() {
		}
	}

	@MessagePackUnpackable
	static class PackageModifierClass {
	}

	@Test
	public void testFinalClassAndAbstractClass() throws Exception {
		try {
			PackUnpackUtil.newEnhancedInstance(FinalModifierClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			PackUnpackUtil.newEnhancedInstance(AbstractModifierClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@MessagePackUnpackable
	public final static class FinalModifierClass {
	}

	@MessagePackUnpackable
	public abstract static class AbstractModifierClass {
	}

	@Test
	public void testInterfaceAndEnumType() throws Exception {
		try {
			PackUnpackUtil.newEnhancedInstance(SampleInterface.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			PackUnpackUtil.newEnhancedInstance(SampleEnum.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@MessagePackUnpackable
	public interface SampleInterface {
	}

	@MessagePackUnpackable
	public enum SampleEnum {
	}

	@Test
	public void testFieldModifiers01() throws Exception {
		FieldModifiersClass src = (FieldModifiersClass) PackUnpackUtil
				.newEnhancedInstance(FieldModifiersClass.class);
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		FieldModifiersClass dst = (FieldModifiersClass) PackUnpackUtil
				.newEnhancedInstance(FieldModifiersClass.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 == dst.f3);
		assertTrue(src.f4 != dst.f4);
	}

	@Test
	public void testFieldModifiers02() throws Exception {
		FieldModifiersClass src = (FieldModifiersClass) PackUnpackUtil
				.newEnhancedInstance(FieldModifiersClass.class);
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		FieldModifiersClass dst = (FieldModifiersClass) PackUnpackUtil
				.initEnhancedInstance(mpo, FieldModifiersClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 == dst.f3);
		assertTrue(src.f4 != dst.f4);
		assertFalse(it.hasNext());
	}

	@MessagePackUnpackable
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
	public void testNestedAnnotatedFieldClass01() throws Exception {
		NestedClass src2 = (NestedClass) PackUnpackUtil
				.newEnhancedInstance(NestedClass.class);
		BaseClass src = (BaseClass) PackUnpackUtil
				.newEnhancedInstance(BaseClass.class);
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		NestedClass dst2 = (NestedClass) PackUnpackUtil
				.newEnhancedInstance(NestedClass.class);
		BaseClass dst = (BaseClass) PackUnpackUtil
				.newEnhancedInstance(BaseClass.class);
		dst.f1 = dst2;
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src2.f2 == dst.f1.f2);
	}

	@Test
	public void testNestedAnnotatedFieldClass02() throws Exception {
		NestedClass src2 = (NestedClass) PackUnpackUtil
				.newEnhancedInstance(NestedClass.class);
		BaseClass src = (BaseClass) PackUnpackUtil
				.newEnhancedInstance(BaseClass.class);
		src.f0 = 0;
		src2.f2 = 2;
		src.f1 = src2;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		NestedClass dst2 = (NestedClass) PackUnpackUtil
				.newEnhancedInstance(NestedClass.class);
		BaseClass dst = (BaseClass) PackUnpackUtil
				.newEnhancedInstance(BaseClass.class);
		dst.f1 = dst2;
		dst = (BaseClass) PackUnpackUtil.initEnhancedInstance(mpo, dst);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src2.f2 == dst.f1.f2);
		assertFalse(it.hasNext());
	}

	@MessagePackUnpackable
	public static class BaseClass {
		public int f0;
		public NestedClass f1;

		public BaseClass() {
		}
	}

	@MessagePackUnpackable
	public static class NestedClass {
		public int f2;

		public NestedClass() {
		}
	}

	@Test
	public void testExtendedClass01() throws Exception {
		SampleSubClass src = (SampleSubClass) PackUnpackUtil
				.newEnhancedInstance(SampleSubClass.class);
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f8 = 8;
		src.f9 = 9;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		SampleSubClass dst = (SampleSubClass) PackUnpackUtil
				.newEnhancedInstance(SampleSubClass.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		pac.unpack((MessageUnpackable) dst);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 == dst.f3);
		assertTrue(src.f4 != dst.f4);
		assertTrue(src.f5 == dst.f5);
		assertTrue(src.f6 == dst.f6);
		assertTrue(src.f8 == dst.f8);
		assertTrue(src.f9 != dst.f9);
	}
	
	@Test
	public void testExtendedClass02() throws Exception {
		SampleSubClass src = (SampleSubClass) PackUnpackUtil
				.newEnhancedInstance(SampleSubClass.class);
		src.f0 = 0;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f8 = 8;
		src.f9 = 9;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertTrue(it.hasNext());
		MessagePackObject mpo = it.next();
		SampleSubClass dst = (SampleSubClass) PackUnpackUtil
				.initEnhancedInstance(mpo, SampleSubClass.class);
		assertTrue(src.f0 == dst.f0);
		assertTrue(src.f1 == dst.f1);
		assertTrue(src.f2 != dst.f2);
		assertTrue(src.f3 == dst.f3);
		assertTrue(src.f4 != dst.f4);
		assertTrue(src.f5 == dst.f5);
		assertTrue(src.f6 == dst.f6);
		assertTrue(src.f8 == dst.f8);
		assertTrue(src.f9 != dst.f9);
		assertFalse(it.hasNext());
	}

	@MessagePackUnpackable
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
		private int f7;
		protected int f8;
		int f9;

		public SampleSuperClass() {
		}
	}
}
