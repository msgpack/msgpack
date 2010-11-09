package org.msgpack.template;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.junit.Test;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

import junit.framework.TestCase;

public class TestPackUnpack extends TestCase {
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = IntegerTemplate.getInstance();
		Integer dst = (Integer) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	@Test
	public void testNullInteger() throws Exception {
		Integer src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
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
		tmpl = new NullableTemplate(IntegerTemplate.getInstance());
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
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = LongTemplate.getInstance();
		Long dst = (Long) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	@Test
	public void testNullLong() throws Exception {
		Long src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
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
		tmpl = new NullableTemplate(LongTemplate.getInstance());
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
		new Packer(out).pack((Object) src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = BigIntegerTemplate.getInstance();
		BigInteger dst = (BigInteger) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	@Test
	public void testNullBigInteger() throws Exception {
		BigInteger src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
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
		tmpl = new NullableTemplate(BigIntegerTemplate.getInstance());
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
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = FloatTemplate.getInstance();
		Float dst = (Float) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst, 10e-10);
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
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = DoubleTemplate.getInstance();
		Double dst = (Double) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst, 10e-10);
	}

	@Test
	public void testNullDouble() throws Exception {
		Double src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
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
		tmpl = new NullableTemplate(DoubleTemplate.getInstance());
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
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = BooleanTemplate.getInstance();
		Boolean dst = (Boolean) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	@Test
	public void testNullBoolean() throws Exception {
		Boolean src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
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
		tmpl = new NullableTemplate(BooleanTemplate.getInstance());
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
		new Packer(out).pack(src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Template tmpl = StringTemplate.getInstance();
		String dst = (String) tmpl.unpack(new Unpacker(in));
		assertEquals(src, dst);
	}

	@Test
	public void testNullString() throws Exception {
		String src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(src);
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
		tmpl = new NullableTemplate(StringTemplate.getInstance());
		dst = (String) tmpl.unpack(unpacker);
		assertEquals(src, dst);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testList() throws Exception {
		List<Integer> emptyList = new ArrayList<Integer>();
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(emptyList);
			ByteArrayInputStream in = new ByteArrayInputStream(out
					.toByteArray());
			Template tmpl = new ListTemplate(IntegerTemplate.getInstance());
			List<Integer> dst = (List<Integer>) tmpl.unpack(new Unpacker(in));
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
			ByteArrayInputStream in = new ByteArrayInputStream(out
					.toByteArray());
			Template tmpl = new ListTemplate(IntegerTemplate.getInstance());
			List<Integer> dst = (List<Integer>) tmpl.unpack(new Unpacker(in));
			assertEquals(len, dst.size());
			for (int j = 0; j < len; j++) {
				assertEquals(l.get(j), dst.get(j));
			}
		}

		for (int i = 0; i < 1000; i++) {
			List<String> l = new ArrayList<String>();
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++)
				l.add(Integer.toString(j));
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(l);
			ByteArrayInputStream in = new ByteArrayInputStream(out
					.toByteArray());
			Template tmpl = new ListTemplate(StringTemplate.getInstance());
			List<String> dst = (List<String>) tmpl.unpack(new Unpacker(in));
			assertEquals(len, dst.size());
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
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		List<String> dst = null;
		try {
			tmpl = new ListTemplate(StringTemplate.getInstance());
			unpacker.wrap(bytes);
			dst = (List<String>) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(new ListTemplate(StringTemplate
				.getInstance()));
		dst = (List<String>) tmpl.unpack(unpacker);
		assertEquals(src, dst);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testMap() throws Exception {
		Map<Integer, Integer> emptyMap = new HashMap<Integer, Integer>();
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(emptyMap);
			ByteArrayInputStream in = new ByteArrayInputStream(out
					.toByteArray());
			Template tmpl = new MapTemplate(IntegerTemplate.getInstance(),
					IntegerTemplate.getInstance());
			Map<Integer, Integer> dst = (Map<Integer, Integer>) tmpl
					.unpack(new Unpacker(in));
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
			ByteArrayInputStream in = new ByteArrayInputStream(out
					.toByteArray());
			Template tmpl = new MapTemplate(IntegerTemplate.getInstance(),
					IntegerTemplate.getInstance());
			Map<Integer, Integer> map = (Map<Integer, Integer>) tmpl
					.unpack(new Unpacker(in));
			assertEquals(len, map.size());
			for (Map.Entry<Integer, Integer> pair : map.entrySet()) {
				Integer val = m.get(pair.getKey());
				assertNotNull(val);
				assertEquals(val, pair.getValue());
			}
		}

		for (int i = 0; i < 1000; i++) {
			Map<String, Integer> m = new HashMap<String, Integer>();
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++) {
				m.put(Integer.toString(j), j);
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(m);
			ByteArrayInputStream in = new ByteArrayInputStream(out
					.toByteArray());
			Template tmpl = new MapTemplate(StringTemplate.getInstance(),
					IntegerTemplate.getInstance());
			Map<String, Integer> map = (Map<String, Integer>) tmpl
					.unpack(new Unpacker(in));
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
		byte[] bytes = out.toByteArray();
		Template tmpl = null;
		Unpacker unpacker = new Unpacker();
		Map<String, String> dst = null;
		try {
			tmpl = new MapTemplate(StringTemplate.getInstance(), StringTemplate
					.getInstance());
			unpacker.wrap(bytes);
			dst = (Map<String, String>) tmpl.unpack(unpacker);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(new MapTemplate(StringTemplate
				.getInstance(), StringTemplate.getInstance()));
		dst = (Map<String, String>) tmpl.unpack(unpacker);
		assertEquals(src, dst);
	}
}
