package org.msgpack.packer;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import java.util.Random;

import junit.framework.TestCase;

import org.junit.Test;
import org.msgpack.MessagePacker;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
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

public class TestPackUnpack extends TestCase {

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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src.byteValue(), unpacker.unpackByte());
	}

	@Test
	public void testNullByte() throws Exception {
		Byte src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(BytePacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Byte dst = null;
		try {
			tmpl = ByteTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (Byte) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(ByteTemplate.getInstance());
		dst = (Byte) tmpl.unpack(unpacker);
		assertEquals(src, dst);
	}

	@Test
	public void testSort() throws Exception {
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src.shortValue(), unpacker.unpackShort());
	}

	@Test
	public void testNullShort() throws Exception {
		Short src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(ShortPacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Short dst = null;
		try {
			tmpl = ShortTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (Short) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(ShortTemplate.getInstance());
		dst = (Short) tmpl.unpack(unpacker);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src.intValue(), unpacker.unpackInt());
	}

	@Test
	public void testNullInteger() throws Exception {
		Integer src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(IntegerPacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Integer dst = null;
		try {
			tmpl = IntegerTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (Integer) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(IntegerTemplate.getInstance());
		dst = (Integer) tmpl.unpack(unpacker);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src.longValue(), unpacker.unpackLong());
	}

	@Test
	public void testNullLong() throws Exception {
		Integer src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(LongPacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Long dst = null;
		try {
			tmpl = LongTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (Long) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(LongTemplate.getInstance());
		dst = (Long) tmpl.unpack(unpacker);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src, unpacker.unpackBigInteger());
	}

	@Test
	public void testNullBigInteger() throws Exception {
		BigInteger src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(BigIntegerPacker
				.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		BigInteger dst = null;
		try {
			tmpl = BigIntegerTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (BigInteger) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(BigIntegerTemplate.getInstance());
		dst = (BigInteger) tmpl.unpack(unpacker);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src.floatValue(), unpacker.unpackFloat(), 10e-10);
	}

	@Test
	public void testNullFloat() throws Exception {
		Float src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(FloatPacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Float dst = null;
		try {
			tmpl = FloatTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (Float) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(FloatTemplate.getInstance());
		dst = (Float) tmpl.unpack(unpacker);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src.doubleValue(), unpacker.unpackDouble(), 10e-10);
	}

	@Test
	public void testNullDouble() throws Exception {
		Double src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(DoublePacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Double dst = null;
		try {
			tmpl = DoubleTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (Double) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(DoubleTemplate.getInstance());
		dst = (Double) tmpl.unpack(unpacker);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src.booleanValue(), unpacker.unpackBoolean());
	}

	@Test
	public void testNullBoolean() throws Exception {
		Boolean src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(BooleanPacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Boolean dst = null;
		try {
			tmpl = BooleanTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (Boolean) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(BooleanTemplate.getInstance());
		dst = (Boolean) tmpl.unpack(unpacker);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker unpacker = new Unpacker(in);
		assertEquals(src, unpacker.unpackString());
	}

	@Test
	public void testNullString() throws Exception {
		String src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		MessagePacker packer = new OptionalPacker(StringPacker.getInstance());
		packer.pack(new Packer(out), src);
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		String dst = null;
		try {
			tmpl = StringTemplate.getInstance();
			unpacker.wrap(bytes);
			dst = (String) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new OptionalTemplate(StringTemplate.getInstance());
		dst = (String) tmpl.unpack(unpacker);
		assertEquals(src, dst);
	}
}
