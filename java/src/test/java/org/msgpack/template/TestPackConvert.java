package org.msgpack.template;

import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.junit.Test;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Util;

import junit.framework.TestCase;

public class TestPackConvert extends TestCase {

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
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = IntegerTemplate.getInstance();
		Integer dst = (Integer) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testNullInteger() throws Exception {
		Integer src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = IntegerTemplate.getInstance();
		Integer dst = null;
		try {
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

	public void _testLong(Long src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = LongTemplate.getInstance();
		Long dst = (Long) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testNullLong() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = LongTemplate.getInstance();
		Long dst = null;
		try {
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
	public void testBiginteger() throws Exception {
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
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = BigIntegerTemplate.getInstance();
		BigInteger dst = (BigInteger) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testNullBigInteger() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = BigIntegerTemplate.getInstance();
		BigInteger dst = null;
		try {
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
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = FloatTemplate.getInstance();
		Float dst = (Float) tmpl.convert(obj);
		assertEquals(src, dst, 10e-10);
	}

	@Test
	public void testNullFloat() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = FloatTemplate.getInstance();
		Float dst = null;
		try {
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
		for (int i = 0; i < 1000; i++) {
			_testDouble(rand.nextDouble());
		}
	}

	static void _testDouble(Double src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = DoubleTemplate.getInstance();
		Double dst = (Double) tmpl.convert(obj);
		assertEquals(src, dst, 10e-10);
	}

	@Test
	public void testNullDouble() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = DoubleTemplate.getInstance();
		Double dst = null;
		try {
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
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = BooleanTemplate.getInstance();
		Boolean dst = (Boolean) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testNullBoolean() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = BooleanTemplate.getInstance();
		Boolean dst = null;
		try {
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
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = StringTemplate.getInstance();
		String dst = (String) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@Test
	public void testNullString() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = StringTemplate.getInstance();
		String dst = null;
		try {
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

	@SuppressWarnings("unchecked")
	@Test
	public void testList() throws Exception {
		List<Integer> emptyList = new ArrayList<Integer>();
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(emptyList);
			MessagePackObject obj = Util.unpackOne(out.toByteArray());
			Template tmpl = new ListTemplate(IntegerTemplate.getInstance());
			List<Integer> dst = (List<Integer>) tmpl.convert(obj);
			assertEquals(emptyList, dst);
		}

		for (int i = 0; i < 1000; i++) {
			List<Integer> l = new ArrayList<Integer>();
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++) {
				l.add(j);
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(l);
			MessagePackObject obj = Util.unpackOne(out.toByteArray());
			Template tmpl = new ListTemplate(IntegerTemplate.getInstance());
			List<Integer> dst = (List<Integer>) tmpl.convert(obj);
			assertEquals(l.size(), dst.size());
			for (int j = 0; j < len; j++) {
				assertEquals(l.get(j), dst.get(j));
			}
		}

		for (int i = 0; i < 1000; i++) {
			List<String> l = new ArrayList<String>();
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++) {
				l.add(Integer.toString(j));
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(l);
			MessagePackObject obj = Util.unpackOne(out.toByteArray());
			Template tmpl = new ListTemplate(StringTemplate.getInstance());
			List<String> dst = (List<String>) tmpl.convert(obj);
			assertEquals(l.size(), dst.size());
			for (int j = 0; j < len; j++) {
				assertEquals(l.get(j), dst.get(j));
			}
		}
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testNullList() throws Exception {
		List<String> src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = new ListTemplate(StringTemplate.getInstance());
		List<String> dst = null;
		try {
			dst = (List<String>) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(new ListTemplate(StringTemplate
				.getInstance()));
		dst = (List<String>) tmpl.convert(obj);
		assertEquals(src, dst);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testMap() throws Exception {
		Map<Integer, Integer> emptyMap = new HashMap<Integer, Integer>();
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(emptyMap);
			MessagePackObject obj = Util.unpackOne(out.toByteArray());
			Template tmpl = new MapTemplate(IntegerTemplate.getInstance(),
					IntegerTemplate.getInstance());
			Map<Integer, Integer> dst = (Map<Integer, Integer>) tmpl
					.convert(obj);
			assertEquals(emptyMap, dst);
		}

		for (int i = 0; i < 1000; i++) {
			Map<Integer, Integer> m = new HashMap<Integer, Integer>();
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++) {
				m.put(j, j);
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(m);
			MessagePackObject obj = Util.unpackOne(out.toByteArray());
			Template tmpl = new MapTemplate(IntegerTemplate.getInstance(),
					IntegerTemplate.getInstance());
			Map<Integer, Integer> map = (Map<Integer, Integer>) tmpl
					.convert(obj);
			assertEquals(m.size(), map.size());
			for (Map.Entry<Integer, Integer> pair : map.entrySet()) {
				Integer val = m.get(pair.getKey());
				assertNotNull(val);
				assertEquals(val, pair.getValue());
			}
		}

		for (int i = 0; i < 1000; i++) {
			Map<String, Integer> m = new HashMap<String, Integer>();
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++)
				m.put(Integer.toString(j), j);
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(m);
			MessagePackObject obj = Util.unpackOne(out.toByteArray());
			Template tmpl = new MapTemplate(StringTemplate.getInstance(),
					IntegerTemplate.getInstance());
			Map<String, Integer> map = (Map<String, Integer>) tmpl.convert(obj);
			assertEquals(m.size(), map.size());
			for (Map.Entry<String, Integer> pair : map.entrySet()) {
				Integer val = m.get(pair.getKey());
				assertNotNull(val);
				assertEquals(val, pair.getValue());
			}
		}
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testNullMap() throws Exception {
		Map<String, String> src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
		MessagePackObject obj = Util.unpackOne(out.toByteArray());
		Template tmpl = new MapTemplate(StringTemplate.getInstance(),
				StringTemplate.getInstance());
		Map<String, String> dst = null;
		try {
			dst = (Map<String, String>) tmpl.convert(obj);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		obj = Util.unpackOne(out.toByteArray());
		tmpl = new OptionalTemplate(new MapTemplate(StringTemplate
				.getInstance(), StringTemplate.getInstance()));
		dst = (Map<String, String>) tmpl.convert(obj);
		assertEquals(src, dst);
	}
}
