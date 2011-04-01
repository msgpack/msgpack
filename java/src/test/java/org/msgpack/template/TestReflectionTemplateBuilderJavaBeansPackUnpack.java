package org.msgpack.template;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.hamcrest.CoreMatchers;
import org.hamcrest.Matcher;
import org.junit.Ignore;
import org.junit.Test;

import org.msgpack.MessagePack;
import org.msgpack.MessagePackable;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.annotation.MessagePackBeans;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.msgpack.annotation.Optional;
import org.msgpack.template.TestTemplateBuilderPackConvert.SampleInterface;
import org.msgpack.template.builder.BuilderSelectorRegistry;
import org.msgpack.template.builder.MessagePackBeansBuilderSelector;
import org.msgpack.template.builder.MessagePackMessageBuilderSelector;
import org.msgpack.template.builder.TemplateBuilder;

import org.junit.Assert;
import junit.framework.TestCase;
import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.assertThat;

public class TestReflectionTemplateBuilderJavaBeansPackUnpack extends TestCase {
	static {
		//Replace template selectors from javassist to reflection.
		BuilderSelectorRegistry instance = BuilderSelectorRegistry.getInstance();

		instance.replace(
				new MessagePackMessageBuilderSelector(
						new ReflectionTemplateBuilder()));
		instance.setForceBuilder( new ReflectionTemplateBuilder());
		instance.replace(new MessagePackBeansBuilderSelector(
				new BeansReflectionTemplateBuilder()));
		
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
	
	Matcher<Object> beansEquals(Object actual){
		return new BeansEquals(actual); 
	}
	Matcher<Object> beansEquals(Object actual,String[] ignoreNames){
		return new BeansEquals(actual,ignoreNames); 
	}
	String[] ignoring(String ... strings){
		return strings;
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
		
		
		assertThat(dst,beansEquals(src));
	}

	@Test
	public void testPrimitiveTypeFields01() throws Exception {
		PrimitiveTypeFieldsClass src = new PrimitiveTypeFieldsClass();

		byte[] raw = MessagePack.pack(src);

		PrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);

		assertThat(dst,beansEquals(src));
	}

	@Test
	public void testPrimitiveTypeFields02() throws Exception {
		PrimitiveTypeFieldsClass src = null;

		byte[] raw = MessagePack.pack(src);

		PrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, PrimitiveTypeFieldsClass.class);
		
		assertThat(dst,beansEquals(src));
	}

	@MessagePackBeans
	public static class PrimitiveTypeFieldsClass {
		byte f0;
		short f1;
		int f2;
		long f3;
		float f4;
		double f5;
		boolean f6;

		public byte getF0() {
			return f0;
		}

		public void setF0(byte f0) {
			this.f0 = f0;
		}

		public short getF1() {
			return f1;
		}

		public void setF1(short f1) {
			this.f1 = f1;
		}

		public int getF2() {
			return f2;
		}

		public void setF2(int f2) {
			this.f2 = f2;
		}

		public long getF3() {
			return f3;
		}

		public void setF3(long f3) {
			this.f3 = f3;
		}

		public float getF4() {
			return f4;
		}

		public void setF4(float f4) {
			this.f4 = f4;
		}

		public double getF5() {
			return f5;
		}

		public void setF5(double f5) {
			this.f5 = f5;
		}

		public boolean isF6() {
			return f6;
		}

		public void setF6(boolean f6) {
			this.f6 = f6;
		}

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
		

		assertThat(dst,beansEquals(src));
	}

	@Test
	public void testOptionalPrimitiveTypeFields02() throws Exception {
		OptionalPrimitiveTypeFieldsClass src = null;

		byte[] raw = MessagePack.pack(src);

		OptionalPrimitiveTypeFieldsClass dst =
			MessagePack.unpack(raw, OptionalPrimitiveTypeFieldsClass.class);
		assertEquals(src, dst);
	}

	@MessagePackBeans
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

		@Optional
		public byte getF0() {
			return f0;
		}

		@Optional
		public void setF0(byte f0) {
			this.f0 = f0;
		}

		@Optional
		public short getF1() {
			return f1;
		}

		public void setF1(short f1) {
			this.f1 = f1;
		}

		public int getF2() {
			return f2;
		}

		@Optional
		public void setF2(int f2) {
			this.f2 = f2;
		}

		@Optional
		public long getF3() {
			return f3;
		}

		public void setF3(long f3) {
			this.f3 = f3;
		}

		@Optional
		public float getF4() {
			return f4;
		}

		public void setF4(float f4) {
			this.f4 = f4;
		}

		@Optional
		public double getF5() {
			return f5;
		}

		public void setF5(double f5) {
			this.f5 = f5;
		}

		@Optional
		public boolean isF6() {
			return f6;
		}

		public void setF6(boolean f6) {
			this.f6 = f6;
		}

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
		

		assertThat(dst,beansEquals(src));
		
	}

	@Test
	public void testGeneralReferenceTypeFieldsClass01() throws Exception {
		GeneralReferenceTypeFieldsClass src = null;

		byte[] raw = MessagePack.pack(src);

		GeneralReferenceTypeFieldsClass dst =
			MessagePack.unpack(raw, GeneralReferenceTypeFieldsClass.class);
		assertEquals(src, dst);
	}

	@MessagePackBeans
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

		public Byte getF0() {
			return f0;
		}

		public void setF0(Byte f0) {
			this.f0 = f0;
		}

		public Short getF1() {
			return f1;
		}

		public void setF1(Short f1) {
			this.f1 = f1;
		}

		public Integer getF2() {
			return f2;
		}

		public void setF2(Integer f2) {
			this.f2 = f2;
		}

		public Long getF3() {
			return f3;
		}

		public void setF3(Long f3) {
			this.f3 = f3;
		}

		public Float getF4() {
			return f4;
		}

		public void setF4(Float f4) {
			this.f4 = f4;
		}

		public Double getF5() {
			return f5;
		}

		public void setF5(Double f5) {
			this.f5 = f5;
		}

		public Boolean getF6() {
			return f6;
		}

		public void setF6(Boolean f6) {
			this.f6 = f6;
		}

		public BigInteger getF7() {
			return f7;
		}

		public void setF7(BigInteger f7) {
			this.f7 = f7;
		}

		public String getF8() {
			return f8;
		}

		public void setF8(String f8) {
			this.f8 = f8;
		}

		public byte[] getF9() {
			return f9;
		}

		public void setF9(byte[] f9) {
			this.f9 = f9;
		}

		public ByteBuffer getF10() {
			return f10;
		}

		public void setF10(ByteBuffer f10) {
			this.f10 = f10;
		}

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


		assertThat(dst,beansEquals(src));
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
		

		assertThat(dst,beansEquals(src));
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

	@MessagePackBeans
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

		@Optional
		public Byte getF0() {
			return f0;
		}

		@Optional
		public void setF0(Byte f0) {
			this.f0 = f0;
		}

		@Optional
		public Short getF1() {
			return f1;
		}

		public void setF1(Short f1) {
			this.f1 = f1;
		}

		public Integer getF2() {
			return f2;
		}

		@Optional
		public void setF2(Integer f2) {
			this.f2 = f2;
		}

		@Optional
		public Long getF3() {
			return f3;
		}

		public void setF3(Long f3) {
			this.f3 = f3;
		}

		@Optional
		public Float getF4() {
			return f4;
		}

		public void setF4(Float f4) {
			this.f4 = f4;
		}

		@Optional
		public Double getF5() {
			return f5;
		}

		public void setF5(Double f5) {
			this.f5 = f5;
		}

		@Optional
		public Boolean getF6() {
			return f6;
		}

		public void setF6(Boolean f6) {
			this.f6 = f6;
		}

		@Optional
		public BigInteger getF7() {
			return f7;
		}

		public void setF7(BigInteger f7) {
			this.f7 = f7;
		}

		@Optional
		public String getF8() {
			return f8;
		}

		public void setF8(String f8) {
			this.f8 = f8;
		}

		@Optional
		public byte[] getF9() {
			return f9;
		}

		public void setF9(byte[] f9) {
			this.f9 = f9;
		}

		@Optional
		public ByteBuffer getF10() {
			return f10;
		}

		public void setF10(ByteBuffer f10) {
			this.f10 = f10;
		}

		public GeneralOptionalReferenceTypeFieldsClass() {
		}
	}

	@Test
	public void testListTypes00() throws Exception {
		SampleListTypes src = new SampleListTypes();
		src.integerListSize0 = new ArrayList<Integer>();
		src.integerList = new ArrayList<Integer>();
		src.integerList.add(1);
		src.integerList.add(2);
		src.integerList.add(3);
		src.stringList = new ArrayList<String>();
		src.stringList.add("e1");
		src.stringList.add("e2");
		src.stringList.add("e3");
		src.stringListList = new ArrayList<List<String>>();
		src.stringListList.add(src.stringList);
		src.sampleListNestedTypeList = new ArrayList<SampleListNestedType>();
		SampleListNestedType slnt = new SampleListNestedType();
		slnt.f0 = new byte[] { 0x01, 0x02 };
		slnt.f1 = "muga";
		src.sampleListNestedTypeList.add(slnt);
		src.byteBufferList = new ArrayList<ByteBuffer>();
		src.byteBufferList.add(ByteBuffer.wrap("e1".getBytes()));
		src.byteBufferList.add(ByteBuffer.wrap("e2".getBytes()));
		src.byteBufferList.add(ByteBuffer.wrap("e3".getBytes()));

		byte[] raw = MessagePack.pack(src);

		SampleListTypes dst =
			MessagePack.unpack(raw, SampleListTypes.class);

		//ignore sampleListNestedTypeList,
		//because SampleListNestedType is not implemented equals() correctly.
		assertThat(dst,beansEquals(src, ignoring("getF4")));
		
		assertEquals(src.sampleListNestedTypeList.size(), dst.sampleListNestedTypeList.size());
		for (int i = 0; i < src.sampleListNestedTypeList.size(); ++i) {
			SampleListNestedType s = src.sampleListNestedTypeList.get(i);
			SampleListNestedType d = dst.sampleListNestedTypeList.get(i);
			assertEquals(s.f0[0], d.f0[0]);
			assertEquals(s.f0[1], d.f0[1]);
			assertEquals(s.f1, d.f1);
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

	@MessagePackBeans
	public static class SampleListTypes {
		public List<Integer> integerListSize0;
		public List<Integer> integerList;
		public List<String> stringList;
		public List<List<String>> stringListList;
		public List<SampleListNestedType> sampleListNestedTypeList;
		public List<ByteBuffer> byteBufferList;

		public List<Integer> getF0() {
			return integerListSize0;
		}

		public void setF0(List<Integer> f0) {
			this.integerListSize0 = f0;
		}

		public List<Integer> getF1() {
			return integerList;
		}

		public void setF1(List<Integer> f1) {
			this.integerList = f1;
		}

		public List<String> getF2() {
			return stringList;
		}

		public void setF2(List<String> f2) {
			this.stringList = f2;
		}

		public List<List<String>> getF3() {
			return stringListList;
		}

		public void setF3(List<List<String>> f3) {
			this.stringListList = f3;
		}

		public List<SampleListNestedType> getF4() {
			return sampleListNestedTypeList;
		}

		public void setF4(List<SampleListNestedType> f4) {
			this.sampleListNestedTypeList = f4;
		}

		public List<ByteBuffer> getF5() {
			return byteBufferList;
		}

		public void setF5(List<ByteBuffer> f5) {
			this.byteBufferList = f5;
		}

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

	@MessagePackBeans
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

		@Optional
		public List<Integer> getF0() {
			return f0;
		}

		@Optional
		public void setF0(List<Integer> f0) {
			this.f0 = f0;
		}

		@Optional
		public List<Integer> getF1() {
			return f1;
		}

		public void setF1(List<Integer> f1) {
			this.f1 = f1;
		}

		public List<String> getF2() {
			return f2;
		}

		@Optional
		public void setF2(List<String> f2) {
			this.f2 = f2;
		}

		@Optional
		public List<List<String>> getF3() {
			return f3;
		}

		public void setF3(List<List<String>> f3) {
			this.f3 = f3;
		}

		@Optional
		public List<SampleOptionalListNestedType> getF4() {
			return f4;
		}

		public void setF4(List<SampleOptionalListNestedType> f4) {
			this.f4 = f4;
		}

		@Optional
		public List<ByteBuffer> getF5() {
			return f5;
		}

		public void setF5(List<ByteBuffer> f5) {
			this.f5 = f5;
		}

		public SampleOptionalListTypes() {
		}
	}

	@MessagePackBeans
	public static class SampleOptionalListNestedType {
		@Optional
		public byte[] f0;
		@Optional
		public String f1;

		@Optional
		public byte[] getF0() {
			return f0;
		}

		public void setF0(byte[] f0) {
			this.f0 = f0;
		}

		@Optional
		public String getF1() {
			return f1;
		}

		public void setF1(String f1) {
			this.f1 = f1;
		}

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

	@MessagePackBeans
	public static class SampleMapTypes {
		public Map<Integer, Integer> f0;
		public Map<Integer, Integer> f1;
		public Map<String, Integer> f2;

		public Map<Integer, Integer> getF0() {
			return f0;
		}

		public void setF0(Map<Integer, Integer> f0) {
			this.f0 = f0;
		}

		public Map<Integer, Integer> getF1() {
			return f1;
		}

		public void setF1(Map<Integer, Integer> f1) {
			this.f1 = f1;
		}

		public Map<String, Integer> getF2() {
			return f2;
		}

		public void setF2(Map<String, Integer> f2) {
			this.f2 = f2;
		}

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

	@MessagePackBeans
	public static class SampleOptionalMapTypes {
		@Optional
		public Map<Integer, Integer> f0;
		@Optional
		public Map<Integer, Integer> f1;
		@Optional
		public Map<String, Integer> f2;

		@Optional
		public Map<Integer, Integer> getF0() {
			return f0;
		}

		public void setF0(Map<Integer, Integer> f0) {
			this.f0 = f0;
		}

		@Optional
		public Map<Integer, Integer> getF1() {
			return f1;
		}

		public void setF1(Map<Integer, Integer> f1) {
			this.f1 = f1;
		}

		@Optional
		public Map<String, Integer> getF2() {
			return f2;
		}

		public void setF2(Map<String, Integer> f2) {
			this.f2 = f2;
		}

		public SampleOptionalMapTypes() {
		}
	}


	@MessagePackBeans
	public abstract static class AbstractModifierClass {
	}

	@Test
	public void testInterfaceType00() throws Exception {
		try {
			TemplateBuilder builder = BuilderSelectorRegistry.getInstance().select(SampleInterface.class);
			Assert.assertNull(builder);
			BuilderSelectorRegistry.getInstance().getForceBuilder().buildTemplate(SampleInterface.class);
			fail();
		} catch (TemplateBuildException e) {
			assertTrue(true);
		}
		assertTrue(true);
	}

	@Test
	public void testInterfaceType01() throws Exception {
		try {
			TemplateBuilder builder = BuilderSelectorRegistry.getInstance().select(SampleInterface.class);
			Assert.assertNull(builder);
			BuilderSelectorRegistry.getInstance().getForceBuilder().buildTemplate(SampleInterface.class);
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
		src.f0 = 23;
		src.f1 = SampleEnum.ONE;

		byte[] raw = MessagePack.pack(src);

		SampleEnumFieldClass dst =
			MessagePack.unpack(raw, SampleEnumFieldClass.class);
		Assert.assertThat(dst.f0, is(src.f0));
		Assert.assertThat(dst.f1, is(src.f1));
	}

	@Test
	public void testEnumTypeForOrdinal01() throws Exception {
		SampleEnumFieldClass src = null;

		byte[] raw = MessagePack.pack(src);

		SampleEnumFieldClass dst =
			MessagePack.unpack(raw, SampleEnumFieldClass.class);
		Assert.assertThat(dst,is(src));
	}

	@MessagePackBeans
	public static class SampleEnumFieldClass {
		public int f0;

		public SampleEnum f1;

		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		public SampleEnum getF1() {
			return f1;
		}

		public void setF1(SampleEnum f1) {
			this.f1 = f1;
		}

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

	@MessagePackBeans
	public static class SampleOptionalEnumFieldClass {
		@Optional
		public int f0;

		@Optional
		public SampleOptionalEnum f1;

		@Optional
		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		@Optional
		public SampleOptionalEnum getF1() {
			return f1;
		}

		public void setF1(SampleOptionalEnum f1) {
			this.f1 = f1;
		}

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
		Assert.assertEquals(src.f1,dst.f1);
		Assert.assertThat(dst.f2, is( not(src.f2)));
		Assert.assertThat(dst.f3, is( not(src.f3)));
		Assert.assertThat(dst.f4, is( not(src.f4)));
	}

	@MessagePackBeans
	public static class FieldModifiersClass {
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}
		
		private int getF2() {
			return f2;
		}

		private void setF2(int f2) {
			this.f2 = f2;
		}

		public int getF3() {
			return f3;
		}

		protected void setF3(int f3) {
			this.f3 = f3;
		}

		public int getF4() {
			return f4;
		}

		void setF4(int f4) {
			this.f4 = f4;
		}

		public int getF1() {
			return f1;
		}

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
		Assert.assertThat(dst.f0, is(src.f0));
		Assert.assertThat(dst.f1, is(src.f1));
		Assert.assertThat(dst.f2, is(not(src.f2)));
		Assert.assertThat(dst.f3, is(not(src.f3)));
		Assert.assertThat(dst.f4, is(not(src.f4)));
	}

	@MessagePackBeans
	public static class OptionalFieldModifiersClass {
		@Optional
		public int f0;
		@Optional
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		@Optional
		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		private int getF2() {
			return f2;
		}

		public void setF2(int f2) {
			this.f2 = f2;
		}

		protected int getF3() {
			return f3;
		}

		protected void setF3(int f3) {
			this.f3 = f3;
		}

		public int getF4() {
			return f4;
		}

		void setF4(int f4) {
			this.f4 = f4;
		}

		public int getF1() {
			return f1;
		}

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

	@MessagePackBeans
	public static class BaseClass {
		public int f0;
		public NestedClass f1;

		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		public NestedClass getF1() {
			return f1;
		}

		public void setF1(NestedClass f1) {
			this.f1 = f1;
		}

		public BaseClass() {
		}
	}

	@MessagePackBeans
	public static class NestedClass {
		public int f2;

		public int getF2() {
			return f2;
		}

		public void setF2(int f2) {
			this.f2 = f2;
		}

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

	@MessagePackBeans
	public static class OptionalBaseClass {
		@Optional
		public int f0;
		@Optional
		public OptionalNestedClass f1;

		@Optional
		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		@Optional
		public OptionalNestedClass getF1() {
			return f1;
		}

		public void setF1(OptionalNestedClass f1) {
			this.f1 = f1;
		}

		public OptionalBaseClass() {
		}
	}

	@MessagePackBeans
	public static class OptionalNestedClass {
		@Optional
		public int f2;

		@Optional
		public int getF2() {
			return f2;
		}

		public void setF2(int f2) {
			this.f2 = f2;
		}

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

	@MessagePackBeans
	public static class BaseClass2 {
		public int f0;
		public MessagePackMessageClass2 f1;

		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		public MessagePackMessageClass2 getF1() {
			return f1;
		}

		public void setF1(MessagePackMessageClass2 f1) {
			this.f1 = f1;
		}

		public BaseClass2() {
		}
	}

	@MessagePackBeans
	public static class MessagePackMessageClass2 {
		public int getF2() {
			return f2;
		}

		public void setF2(int f2) {
			this.f2 = f2;
		}

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

	@MessagePackBeans
	public static class OptionalBaseClass2 {
		@Optional
		public int f0;
		@Optional
		public OptionalMessagePackMessageClass2 f1;

		@Optional
		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		@Optional
		public OptionalMessagePackMessageClass2 getF1() {
			return f1;
		}

		public void setF1(OptionalMessagePackMessageClass2 f1) {
			this.f1 = f1;
		}

		public OptionalBaseClass2() {
		}
	}

	@MessagePackBeans
	public static class OptionalMessagePackMessageClass2 {
		@Optional
		public int f2;

		@Optional
		public int getF2() {
			return f2;
		}

		public void setF2(int f2) {
			this.f2 = f2;
		}

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

	@MessagePackBeans
	public static class SampleSubClass extends SampleSuperClass {
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;

		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		public int getF1() {
			return f1;
		}

		public SampleSubClass() {
		}
	}

	@MessagePackBeans
	public static class SampleSuperClass {
		public int f5;
		public final int f6 = 2;
		@SuppressWarnings("unused")
		private int f7;
		protected int f8;
		int f9;

		public int getF5() {
			return f5;
		}

		public void setF5(int f5) {
			this.f5 = f5;
		}

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

	@MessagePackBeans
	public static class SampleOptionalSubClass extends SampleOptionalSuperClass {
		@Optional
		public int f0;
		public final int f1 = 1;
		private int f2;
		protected int f3;
		int f4;
		@Optional
		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		public SampleOptionalSubClass() {
		}
	}

	@MessagePackBeans
	public static class SampleOptionalSuperClass {
		@Optional
		public int getF5() {
			return f5;
		}

		public void setF5(int f5) {
			this.f5 = f5;
		}

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

	@MessagePackBeans
	public static class BaseMessagePackableUnpackableClass {
		public MessagePackableUnpackableClass f0;
		public int f1;
		public List<MessagePackableUnpackableClass> f2;

		public MessagePackableUnpackableClass getF0() {
			return f0;
		}

		public void setF0(MessagePackableUnpackableClass f0) {
			this.f0 = f0;
		}

		public int getF1() {
			return f1;
		}

		public void setF1(int f1) {
			this.f1 = f1;
		}

		public List<MessagePackableUnpackableClass> getF2() {
			return f2;
		}

		public void setF2(List<MessagePackableUnpackableClass> f2) {
			this.f2 = f2;
		}

		public BaseMessagePackableUnpackableClass() {
		}
	}

	@MessagePackBeans
	public static class MessagePackableUnpackableClass implements
			MessagePackable, MessageUnpackable {
		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		public int getF1() {
			return f1;
		}

		public void setF1(int f1) {
			this.f1 = f1;
		}

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

	@MessagePackBeans
	public static class OptionalBaseMessagePackableUnpackableClass {
		@Optional
		public OptionalMessagePackableUnpackableClass f0;
		@Optional
		public int f1;
		@Optional
		public List<OptionalMessagePackableUnpackableClass> f2;

		@Optional
		public OptionalMessagePackableUnpackableClass getF0() {
			return f0;
		}

		public void setF0(OptionalMessagePackableUnpackableClass f0) {
			this.f0 = f0;
		}

		@Optional
		public int getF1() {
			return f1;
		}

		public void setF1(int f1) {
			this.f1 = f1;
		}

		@Optional
		public List<OptionalMessagePackableUnpackableClass> getF2() {
			return f2;
		}

		public void setF2(List<OptionalMessagePackableUnpackableClass> f2) {
			this.f2 = f2;
		}

		public OptionalBaseMessagePackableUnpackableClass() {
		}
	}

	@MessagePackBeans
	public static class OptionalMessagePackableUnpackableClass implements
			MessagePackable, MessageUnpackable {
		@Optional
		public int getF0() {
			return f0;
		}

		public void setF0(int f0) {
			this.f0 = f0;
		}

		@Optional
		public int getF1() {
			return f1;
		}

		public void setF1(int f1) {
			this.f1 = f1;
		}

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

