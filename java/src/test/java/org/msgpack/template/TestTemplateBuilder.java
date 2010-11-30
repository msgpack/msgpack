package org.msgpack.template;

import java.util.*;
import java.io.*;
import java.math.*;
import org.msgpack.*;
import org.msgpack.annotation.*;

import org.junit.Test;
import junit.framework.TestCase;

public class TestTemplateBuilder extends TestCase {
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

	public static class SampleMapTypes {
		public Map<Integer, Integer> f0;
		public Map<Integer, Integer> f1;
		public Map<String, Integer> f2;

		public SampleMapTypes() {
		}
	}

	static void buildAndRegisterTemplate(Class<?> targetClass) {
		MessagePack.register(targetClass,
				TemplateBuilder.build(targetClass));
	}

	static {
		buildAndRegisterTemplate(PrimitiveTypeFieldsClass.class);
		buildAndRegisterTemplate(GeneralReferenceTypeFieldsClass.class);
		buildAndRegisterTemplate(SampleListNestedType.class);
		buildAndRegisterTemplate(SampleListTypes.class);
		buildAndRegisterTemplate(SampleMapTypes.class);
	}

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

		byte[] raw = MessagePack.pack(src);

		PrimitiveTypeFieldsClass dstu =
			MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
		assertEquals(src.f0, dstu.f0);
		assertEquals(src.f1, dstu.f1);
		assertEquals(src.f2, dstu.f2);
		assertEquals(src.f3, dstu.f3);
		assertEquals(src.f4, dstu.f4);
		assertEquals(src.f5, dstu.f5);
		assertEquals(src.f6, dstu.f6);

		MessagePackObject o = MessagePack.unpack(raw);
		PrimitiveTypeFieldsClass dsto =
			o.convert(PrimitiveTypeFieldsClass.class);

		assertEquals(src.f0, dsto.f0);
		assertEquals(src.f1, dsto.f1);
		assertEquals(src.f2, dsto.f2);
		assertEquals(src.f3, dsto.f3);
		assertEquals(src.f4, dsto.f4);
		assertEquals(src.f5, dsto.f5);
		assertEquals(src.f6, dsto.f6);
	}

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

		byte[] raw = MessagePack.pack(src);

		GeneralReferenceTypeFieldsClass dstu =
				MessagePack.unpack(raw, GeneralReferenceTypeFieldsClass.class);
		assertEquals(src.f0, dstu.f0);
		assertEquals(src.f1, dstu.f1);
		assertEquals(src.f2, dstu.f2);
		assertEquals(src.f3, dstu.f3);
		assertEquals(src.f4, dstu.f4);
		assertEquals(src.f5, dstu.f5);
		assertEquals(src.f6, dstu.f6);
		assertEquals(src.f7, dstu.f7);
		assertEquals(src.f8, dstu.f8);
		assertEquals(src.f9[0], dstu.f9[0]);
		assertEquals(src.f9[1], dstu.f9[1]);

		MessagePackObject o = MessagePack.unpack(raw);
		GeneralReferenceTypeFieldsClass dsto =
			o.convert(GeneralReferenceTypeFieldsClass.class);
		assertEquals(src.f0, dsto.f0);
		assertEquals(src.f1, dsto.f1);
		assertEquals(src.f2, dsto.f2);
		assertEquals(src.f3, dsto.f3);
		assertEquals(src.f4, dsto.f4);
		assertEquals(src.f5, dsto.f5);
		assertEquals(src.f6, dsto.f6);
		assertEquals(src.f7, dsto.f7);
		assertEquals(src.f8, dsto.f8);
		assertEquals(src.f9[0], dsto.f9[0]);
		assertEquals(src.f9[1], dsto.f9[1]);
	}

	@Test
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
		src.f3 = new ArrayList<List<String>>();
		src.f3.add(src.f2);
		src.f4 = new ArrayList<SampleListNestedType>();
		SampleListNestedType slnt = new SampleListNestedType();
		slnt.f0 = new byte[] { 0x01, 0x02 };
		slnt.f1 = "muga";
		src.f4.add(slnt);

		byte[] raw = MessagePack.pack(src);

		SampleListTypes dstu =
				MessagePack.unpack(raw, SampleListTypes.class);
		assertEquals(src.f0.size(), dstu.f0.size());
		assertEquals(src.f1.size(), dstu.f1.size());
		for (int i = 0; i < src.f1.size(); ++i) {
			assertEquals(src.f1.get(i), dstu.f1.get(i));
		}
		assertEquals(src.f2.size(), dstu.f2.size());
		for (int i = 0; i < src.f2.size(); ++i) {
			assertEquals(src.f2.get(i), dstu.f2.get(i));
		}
		assertEquals(src.f3.size(), dstu.f3.size());
		for (int i = 0; i < src.f3.size(); ++i) {
			List<String> srclist = src.f3.get(i);
			List<String> dstlist = dstu.f3.get(i);
			assertEquals(srclist.size(), dstlist.size());
			for (int j = 0; j < srclist.size(); ++j) {
				assertEquals(srclist.get(j), dstlist.get(j));
			}
		}
		assertEquals(src.f4.size(), dstu.f4.size());
		for (int i = 0; i < src.f4.size(); ++i) {
			SampleListNestedType s = src.f4.get(i);
			SampleListNestedType d = dstu.f4.get(i);
			assertEquals(s.f0[0], d.f0[0]);
			assertEquals(s.f0[1], d.f0[1]);
			assertEquals(s.f1, d.f1);
		}
	}

}

