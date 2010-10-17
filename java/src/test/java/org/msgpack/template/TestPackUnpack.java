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
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

import junit.framework.TestCase;

public class TestPackUnpack extends TestCase {
	@Test
	public void testInteger() throws Exception {
		// _testInteger(null); // FIXME
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
	public void testLong() throws Exception {
		// _testLong(null); // FIXME
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
	public void testBigInteger() throws Exception {
		// _testBigInteger(null); // FIXME
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
	public void testFloat() throws Exception {
		// _testFloat(null); // FIXME
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
		// _testDouble(null); // FIXME
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
	public void testBoolean() throws Exception {
		// _testBoolean(null); // FIXME
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
	public void testString() throws Exception {
		// _testString(null); // FIXME
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

	@SuppressWarnings("unchecked")
	@Test
	public void testList() throws Exception {
		// nullList // FIXME
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
	public void testMap() throws Exception {
		// nullMap // FIXME
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
}
