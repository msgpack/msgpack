package org.msgpack.packer;

import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import java.util.Random;

import junit.framework.TestCase;

import org.junit.Test;
import org.msgpack.MessagePackObject;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Util;
import org.msgpack.template.BigIntegerTemplate;
import org.msgpack.template.BooleanTemplate;
import org.msgpack.template.ByteTemplate;
import org.msgpack.template.DoubleTemplate;
import org.msgpack.template.FloatTemplate;
import org.msgpack.template.IntegerTemplate;
import org.msgpack.template.LongTemplate;
import org.msgpack.template.OptionalTemplate;
import org.msgpack.template.ShortTemplate;
import org.msgpack.template.StringTemplate;

public class TestPackConvert extends TestCase {

	@Test
	public void testByte() throws Exception {
		_testByte((byte) 0);
		_testByte((byte) -1);
		_testByte((byte) 1);
		_testByte(Byte.MIN_VALUE);
		_testByte(Byte.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++) {
			_testByte((byte) rand.nextInt());
		}
	}

	static void _testByte(Byte src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = BytePacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src.byteValue(), obj.asByte());
	}

	@Test
	public void testNullByte() throws Exception {
		Byte src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(BytePacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		Byte dst = null;
		try {
			tmpl = ByteTemplate.getInstance();
			dst = (Byte) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(ByteTemplate.getInstance());
		dst = (Byte) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testShort() throws Exception {
		_testShort((short) 0);
		_testShort((short) -1);
		_testShort((short) 1);
		_testShort(Short.MIN_VALUE);
		_testShort(Short.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++) {
			_testShort((short) rand.nextInt());
		}
	}

	static void _testShort(Short src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = ShortPacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src.shortValue(), obj.asShort());
	}

	@Test
	public void testNullShort() throws Exception {
		Short src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(ShortPacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		Short dst = null;
		try {
			tmpl = ShortTemplate.getInstance();
			dst = (Short) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(ShortTemplate.getInstance());
		dst = (Short) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testInteger() throws Exception {
		_testInteger(0);
		_testInteger(-1);
		_testInteger(1);
		_testInteger(Integer.MIN_VALUE);
		_testInteger(Integer.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++) {
			_testInteger(rand.nextInt());
		}
	}

	static void _testInteger(Integer src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = IntegerPacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src.intValue(), obj.asInt());
	}

	@Test
	public void testNullInteger() throws Exception {
		Integer src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(IntegerPacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		Integer dst = null;
		try {
			tmpl = IntegerTemplate.getInstance();
			dst = (Integer) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(IntegerTemplate.getInstance());
		dst = (Integer) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testLong() throws Exception {
		_testLong((long) 0);
		_testLong((long) -1);
		_testLong((long) 1);
		_testLong((long) Integer.MIN_VALUE);
		_testLong((long) Integer.MAX_VALUE);
		_testLong(Long.MIN_VALUE);
		_testLong(Long.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++) {
			_testLong(rand.nextLong());
		}
	}

	static void _testLong(Long src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = LongPacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src.longValue(), obj.asLong());
	}

	@Test
	public void testNullLong() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(LongPacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		Long dst = null;
		try {
			tmpl = LongTemplate.getInstance();
			dst = (Long) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(LongTemplate.getInstance());
		dst = (Long) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testBigInteger() throws Exception {
		_testBigInteger(BigInteger.valueOf(0));
		_testBigInteger(BigInteger.valueOf(-1));
		_testBigInteger(BigInteger.valueOf(1));
		_testBigInteger(BigInteger.valueOf(Integer.MIN_VALUE));
		_testBigInteger(BigInteger.valueOf(Integer.MAX_VALUE));
		_testBigInteger(BigInteger.valueOf(Long.MIN_VALUE));
		_testBigInteger(BigInteger.valueOf(Long.MAX_VALUE));
		BigInteger max = BigInteger.valueOf(Long.MAX_VALUE).setBit(63);
		_testBigInteger(max);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++) {
			_testBigInteger(max.subtract(BigInteger.valueOf(Math.abs(rand
					.nextLong()))));
		}
	}

	static void _testBigInteger(BigInteger src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = BigIntegerPacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src, obj.asBigInteger());
	}

	@Test
	public void testNullBigInteger() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(BigIntegerPacker
				.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		BigInteger dst = null;
		try {
			tmpl = BigIntegerTemplate.getInstance();
			dst = (BigInteger) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(BigIntegerTemplate.getInstance());
		dst = (BigInteger) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testFloat() throws Exception {
		_testFloat((float) 0.0);
		_testFloat((float) -0.0);
		_testFloat((float) 1.0);
		_testFloat((float) -1.0);
		_testFloat((float) Float.MAX_VALUE);
		_testFloat((float) Float.MIN_VALUE);
		_testFloat((float) Float.NaN);
		_testFloat((float) Float.NEGATIVE_INFINITY);
		_testFloat((float) Float.POSITIVE_INFINITY);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++) {
			_testFloat(rand.nextFloat());
		}
	}

	static void _testFloat(Float src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = FloatPacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src.floatValue(), obj.asFloat(), 10e-10);
	}

	@Test
	public void testNullFloat() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(FloatPacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		Float dst = null;
		try {
			tmpl = FloatTemplate.getInstance();
			dst = (Float) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(FloatTemplate.getInstance());
		dst = (Float) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testDouble() throws Exception {
		_testDouble((double) 0.0);
		_testDouble((double) -0.0);
		_testDouble((double) 1.0);
		_testDouble((double) -1.0);
		_testDouble((double) Double.MAX_VALUE);
		_testDouble((double) Double.MIN_VALUE);
		_testDouble((double) Double.NaN);
		_testDouble((double) Double.NEGATIVE_INFINITY);
		_testDouble((double) Double.POSITIVE_INFINITY);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++)
			_testDouble(rand.nextDouble());
	}

	static void _testDouble(Double src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = DoublePacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src.doubleValue(), obj.asDouble(), 10e-10);
	}

	@Test
	public void testNullDouble() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DoublePacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		Double dst = null;
		try {
			tmpl = DoubleTemplate.getInstance();
			dst = (Double) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(DoubleTemplate.getInstance());
		dst = (Double) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testBoolean() throws Exception {
		_testBoolean(false);
		_testBoolean(true);
	}

	static void _testBoolean(Boolean src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = BooleanPacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src.booleanValue(), obj.asBoolean());
	}

	@Test
	public void testNullBoolean() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(BooleanPacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		Boolean dst = null;
		try {
			tmpl = BooleanTemplate.getInstance();
			dst = (Boolean) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(BooleanTemplate.getInstance());
		dst = (Boolean) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testString() throws Exception {
		_testString("");
		_testString("a");
		_testString("ab");
		_testString("abc");

		// small size string
		for (int i = 0; i < 100; i++) {
			StringBuilder sb = new StringBuilder();
			int len = (int) Math.random() % 31 + 1;
			for (int j = 0; j < len; j++) {
				sb.append('a' + ((int) Math.random()) & 26);
			}
			_testString(sb.toString());
		}

		// medium size string
		for (int i = 0; i < 100; i++) {
			StringBuilder sb = new StringBuilder();
			int len = (int) Math.random() % 100 + (1 << 15);
			for (int j = 0; j < len; j++) {
				sb.append('a' + ((int) Math.random()) & 26);
			}
			_testString(sb.toString());
		}

		// large size string
		for (int i = 0; i < 10; i++) {
			StringBuilder sb = new StringBuilder();
			int len = (int) Math.random() % 100 + (1 << 31);
			for (int j = 0; j < len; j++) {
				sb.append('a' + ((int) Math.random()) & 26);
			}
			_testString(sb.toString());
		}
	}

	static void _testString(String src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = StringPacker.getInstance();
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		assertEquals(src, obj.asString());
	}

	@Test
	public void testNullString() throws Exception {
		String src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(StringPacker.getInstance());
		packer.pack(new Packer(out), src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = null;
		String dst = null;
		try {
			tmpl = StringTemplate.getInstance();
			dst = (String) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(StringTemplate.getInstance());
		dst = (String) tmpl.convert(obj);
		assertEquals(src, dst);
	}
}
