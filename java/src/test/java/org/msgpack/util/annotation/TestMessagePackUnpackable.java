package org.msgpack.util.annotation;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.math.BigInteger;

import junit.framework.TestCase;

import org.junit.Test;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class TestMessagePackUnpackable extends TestCase {

	@Test
	public void testGeneralPrimitiveTypeFieldsClass() throws Exception {
		GeneralPrimitiveTypeFieldsClass src = (GeneralPrimitiveTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(GeneralPrimitiveTypeFieldsClass.class);
		src.f0 = (byte) 0;
		src.f1 = 1;
		src.f2 = 2;
		src.f3 = 3;
		src.f4 = 4;
		src.f5 = 5;
		src.f6 = false;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		GeneralPrimitiveTypeFieldsClass dst = (GeneralPrimitiveTypeFieldsClass) PackUnpackUtil
				.newEnhancedInstance(GeneralPrimitiveTypeFieldsClass.class);
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

	@MessagePackUnpackable
	public static class GeneralPrimitiveTypeFieldsClass {
		public byte f0;
		public short f1;
		public int f2;
		public long f3;
		public float f4;
		public double f5;
		public boolean f6;

		public GeneralPrimitiveTypeFieldsClass() {
		}
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass() throws Exception {
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

		public GeneralReferenceTypeFieldsClass() {
		}
	}

	@Test
	public void testPublicDefaultConstructorClass() throws Exception {
		try {
			PackUnpackUtil.newEnhancedInstance(NoDefaultConstructorClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			PackUnpackUtil.newEnhancedInstance(PrivateDefaultConstructorClass.class);
			fail();
		} catch (PackUnpackUtilException e) {
			assertTrue(true);
		}
		assertTrue(true);
		try {
			PackUnpackUtil.newEnhancedInstance(ProtectedDefaultConstructorClass.class);
			assertTrue(true);
		} catch (PackUnpackUtilException e) {
			fail();
		}
		assertTrue(true);
		try {
			PackUnpackUtil.newEnhancedInstance(PackageDefaultConstructorClass.class);
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
	public void testPublicModifierClass() throws Exception {
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
	public void testFinalAndAbstractModifierClass() throws Exception {
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
	public void testInterfaceAndEnum() throws Exception {
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
	public void testFinalFieldClass() throws Exception {

	}

	@Test
	public void testPrivateFieldClass() throws Exception {

	}

	@Test
	public void testProtectedFieldClass() throws Exception {

	}

	@Test
	public void testNonModifierFieldClass() throws Exception {

	}

	@Test
	public void testNestedAnnotatedFieldClass() throws Exception {

	}

	@Test
	public void testSuperClass() throws Exception {

	}
}
