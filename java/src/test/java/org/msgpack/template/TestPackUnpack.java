package org.msgpack.template;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
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
		Template tmpl = IntegerTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Integer dst = (Integer) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst);
	}

	@Test
	public void testNullInteger() throws Exception {
		Template tmpl = IntegerTemplate.getInstance();
		Integer src = null;
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(IntegerTemplate.getInstance());
		Integer dst = (Integer) tmpl.unpack(unpacker, null);
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
		Template tmpl = LongTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Long dst = (Long) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst);
	}

	@Test
	public void testNullLong() throws Exception {
		Long src = null;
		Template tmpl = LongTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(LongTemplate.getInstance());
		Long dst = (Long) tmpl.unpack(unpacker, null);
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
		Template tmpl = BigIntegerTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		BigInteger dst = (BigInteger) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst);
	}

	@Test
	public void testNullBigInteger() throws Exception {
		BigInteger src = null;
		Template tmpl = BigIntegerTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(BigIntegerTemplate.getInstance());
		BigInteger dst = (BigInteger) tmpl.unpack(unpacker, null);
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
		Template tmpl = FloatTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Float dst = (Float) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst, 10e-10);
	}

	@Test
	public void testNullFloat() throws Exception {
		Double src = null;
		Template tmpl = FloatTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(FloatTemplate.getInstance());
		Float dst = (Float) tmpl.unpack(unpacker, null);
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
		Template tmpl = DoubleTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Double dst = (Double) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst, 10e-10);
	}

	@Test
	public void testNullDouble() throws Exception {
		Double src = null;
		Template tmpl = DoubleTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(DoubleTemplate.getInstance());
		Double dst = (Double) tmpl.unpack(unpacker, null);
		assertEquals(src, dst);
	}

	@Test
	public void testBoolean() throws Exception {
		_testBoolean(false);
		_testBoolean(true);
	}

	static void _testBoolean(Boolean src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Template tmpl = BooleanTemplate.getInstance();
		Packer packer = new Packer(out);
		tmpl.pack(packer, src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Boolean dst = (Boolean) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst);
	}

	@Test
	public void testNullBoolean() throws Exception {
		Boolean src = null;
		Template tmpl = BooleanTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(BooleanTemplate.getInstance());
		Boolean dst = (Boolean) tmpl.unpack(unpacker, null);
		assertEquals(src, dst);
	}

	@Test
	public void testByteArray() throws Exception {
		Random rand = new Random(System.currentTimeMillis());
		byte[] b0 = new byte[0];
		_testByteArray(b0);
		byte[] b1 = new byte[10];
		rand.nextBytes(b1);
		_testByteArray(b1);
		byte[] b2 = new byte[1024];
		rand.nextBytes(b2);
		_testByteArray(b2);
	}

	static void _testByteArray(byte[] src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Template tmpl = ByteArrayTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		byte[] dst = (byte[]) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src.length, dst.length);
		for (int i = 0; i < src.length; ++i) {
			assertEquals(src[i], dst[i]);
		}
	}

	@Test
	public void testNullByteArray() throws Exception {
		byte[] src = null;
		Template tmpl = ByteArrayTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(BooleanTemplate.getInstance());
		byte[] dst = (byte[]) tmpl.unpack(unpacker, null);
		assertEquals(null, dst);
	}

	@Test
	public void testByteBuffer() throws Exception {
		Random rand = new Random(System.currentTimeMillis());
		byte[] b0 = new byte[0];
		ByteBuffer bb0 = ByteBuffer.wrap(b0);
		_testByteBuffer(bb0);
		bb0.clear();
		byte[] b1 = new byte[10];
		rand.nextBytes(b1);
		ByteBuffer bb1 = ByteBuffer.wrap(b1);
		_testByteBuffer(bb1);
		bb1.clear();
		byte[] b2 = new byte[2048];
		rand.nextBytes(b2);
		ByteBuffer bb2 = ByteBuffer.wrap(b2);
		_testByteBuffer(bb2);
		bb2.clear();
	}

	static void _testByteBuffer(ByteBuffer src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Template tmpl = ByteBufferTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		ByteBuffer dst = (ByteBuffer) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src.limit() - src.position(), dst.limit() - dst.position());
		int dst_pos = dst.position();
		for (int i = src.position(); i < src.limit(); ++i) {
			assertEquals(src.get(i), dst.get(dst_pos));
			dst_pos++;
		}
	}

	@Test
	public void testNullByteBuffer() throws Exception {
		ByteBuffer src = null;
		Template tmpl = ByteBufferTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(BooleanTemplate.getInstance());
		ByteBuffer dst = (ByteBuffer) tmpl.unpack(unpacker, null);
		assertEquals(null, dst);
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
		Template tmpl = StringTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		String dst = (String) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst);
	}

	@Test
	public void testNullString() throws Exception {
		String src = null;
		Template tmpl = StringTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(StringTemplate.getInstance());
		String dst = (String) tmpl.unpack(unpacker, null);
		assertEquals(src, dst);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testList() throws Exception {
		List<Integer> src = new ArrayList<Integer>();
		Template tmpl = new ListTemplate(IntegerTemplate.getInstance());
		// size is zero
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			List<Integer> dst = (List<Integer>) tmpl.unpack(new Unpacker(in), null);
			assertEquals(src.size(), dst.size());
			Integer[] src_array = src.toArray(new Integer[0]);
			Integer[] dst_array = dst.toArray(new Integer[0]);
			for (int i = 0; i < src_array.length; ++i) {
				assertEquals(src_array[i], dst_array[i]);
			}
			src.clear();
		}

		// otherwise
		{
			int len = (int) (Math.random() * 1000);
			for (int i = 0; i < len; i++) {
				src.add(i);
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			List<Integer> dst = (List<Integer>) tmpl.unpack(new Unpacker(in), null);
			assertEquals(src.size(), dst.size());
			Integer[] src_array = src.toArray(new Integer[0]);
			Integer[] dst_array = dst.toArray(new Integer[0]);
			for (int i = 0; i < src_array.length; ++i) {
				assertEquals(src_array[i], dst_array[i]);
			}
			src.clear();
		}
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testNullList() throws Exception {
		List<String> src = null;
		Template tmpl = new ListTemplate(StringTemplate.getInstance());
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(new ListTemplate(StringTemplate.getInstance()));
		List<String> dst = (List<String>) tmpl.unpack(unpacker, null);
		assertEquals(src, dst);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testMap() throws Exception {
		Map<Integer, Integer> src = new HashMap<Integer, Integer>();
		Template tmpl = new MapTemplate(
				IntegerTemplate.getInstance(),
				IntegerTemplate.getInstance());
		// size is zero
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Map<Integer, Integer> dst = (Map<Integer, Integer>)
				tmpl.unpack(new Unpacker(in), null);
			assertEquals(src.size(), src.size());
			for (Map.Entry<Integer, Integer> pair : dst.entrySet()) {
				Integer val = src.get(pair.getKey());
				assertNotNull(val);
				assertEquals(val, pair.getValue());
			}
			src.clear();
		}

		// otherwise
		{
			int len = (int) (Math.random() * 1000);
			for (int j = 0; j < len; j++) {
				src.put(j, j);
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Map<Integer, Integer> dst = (Map<Integer, Integer>)
				tmpl.unpack(new Unpacker(in), null);
			assertEquals(src.size(), dst.size());
			for (Map.Entry<Integer, Integer> pair : dst.entrySet()) {
				Integer val = src.get(pair.getKey());
				assertNotNull(val);
				assertEquals(val, pair.getValue());
			}
		}
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testNullMap() throws Exception {
		Map<String, String> src = null;
		Template tmpl = new MapTemplate(
				StringTemplate.getInstance(), 
				StringTemplate.getInstance());
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(new MapTemplate(StringTemplate
				.getInstance(), StringTemplate.getInstance()));
		Map<String, String> dst = (Map<String, String>) tmpl.unpack(unpacker, null);
		assertEquals(src, dst);
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testCollectionLinkedList() throws Exception {
		LinkedList<Integer> src = new LinkedList<Integer>();
		Template tmpl = new CollectionTemplate(IntegerTemplate.getInstance());
		// size is zero
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			LinkedList<Integer> dst = (LinkedList<Integer>)
				tmpl.unpack(new Unpacker(in), new LinkedList<Integer>());
			assertEquals(src.getClass(), dst.getClass());
			assertEquals(src.size(), dst.size());
			src.clear();
		}

		// otherwise
		{
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++) {
				src.add(j);
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			LinkedList<Integer> dst = (LinkedList<Integer>)
				tmpl.unpack(new Unpacker(in), new LinkedList<Integer>());
			assertEquals(src.getClass(), dst.getClass());
			assertEquals(src.size(), dst.size());
			for (int j = 0; j < len; j++) {
				assertEquals(src.get(j), dst.get(j));
			}
			src.clear();
		}
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testCollectionHashSet() throws Exception {
		HashSet<Integer> src = new HashSet<Integer>();
		Template tmpl = new CollectionTemplate(IntegerTemplate.getInstance());
		// size is zero
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			HashSet<Integer> dst = (HashSet<Integer>)
				tmpl.unpack(new Unpacker(in), new HashSet<Integer>());
			assertEquals(src.getClass(), dst.getClass());
			assertEquals(src.size(), dst.size());
			src.clear();
		}

		// otherwise
		{
			int len = (int) Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++) {
				src.add(j);
			}
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			tmpl.pack(new Packer(out), src);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			HashSet<Integer> dst = (HashSet<Integer>)
				tmpl.unpack(new Unpacker(in), new HashSet<Integer>());
			assertEquals(src.getClass(), dst.getClass());
			assertEquals(src.size(), dst.size());
			Integer[] src_array = src.toArray(new Integer[0]);
			Integer[] dst_array = dst.toArray(new Integer[0]);
			for (int j = 0; j < len; j++) {
				assertEquals(src_array[j], dst_array[j]);
			}
			src.clear();
		}
	}

	@SuppressWarnings("unchecked")
	@Test
	public void testNullCollection() throws Exception {
		Collection<String> src = null;
		Template tmpl = new CollectionTemplate(StringTemplate.getInstance());
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Throwable t) {
			assertTrue(t instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		unpacker.wrap(bytes);
		try {
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Throwable t) {
			assertTrue(t instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(new CollectionTemplate(StringTemplate.getInstance()));
		Collection<String> dst = (Collection<String>) tmpl.unpack(unpacker, null);
		assertEquals(src, dst);
	}

	@Test
	public void testBigDecimal() throws Exception {
		// String
		_testBigDecimal(new BigDecimal("0"));
		_testBigDecimal(new BigDecimal("-0"));
		_testBigDecimal(new BigDecimal("1"));
		_testBigDecimal(new BigDecimal("-1"));
		_testBigDecimal(new BigDecimal("123.456"));
		_testBigDecimal(new BigDecimal("-123.456"));
		_testBigDecimal(new BigDecimal("0.123456789"));
		_testBigDecimal(new BigDecimal("-0.123456789"));

		// char array
		char[] zero = {'0'};
		_testBigDecimal(new BigDecimal(zero));
		char[] one = {'1'};
		_testBigDecimal(new BigDecimal(one));
		char[] minusOne = {'-', '1'};
		_testBigDecimal(new BigDecimal(minusOne));
		char[] decimal = {'1', '2', '3', '.', '4', '5', '6'};
		_testBigDecimal(new BigDecimal(decimal));
		char[] minusDecimal = {'-', '1', '2', '3', '.', '4', '5', '6'};
		_testBigDecimal(new BigDecimal(minusDecimal));
		char[] oneOrLessDecimal = {'0', '.', '1', '2', '3'};
		_testBigDecimal(new BigDecimal(oneOrLessDecimal));
		char[] minusOneOrLessDecimal = {'-', '0', '.', '1', '2', '3'};
		_testBigDecimal(new BigDecimal(minusOneOrLessDecimal));

		// int
		_testBigDecimal(new BigDecimal(0));
		_testBigDecimal(new BigDecimal(-0));
		_testBigDecimal(new BigDecimal(1));
		_testBigDecimal(new BigDecimal(-1));
		_testBigDecimal(new BigDecimal(Integer.MAX_VALUE));
		_testBigDecimal(new BigDecimal(Integer.MIN_VALUE));

		// double
		_testBigDecimal(new BigDecimal((double) 0.0));
		_testBigDecimal(new BigDecimal((double) -0.0));
		_testBigDecimal(new BigDecimal((double) 1.0));
		_testBigDecimal(new BigDecimal((double) -1.0));
		_testBigDecimal(new BigDecimal((double) 123.456));
		_testBigDecimal(new BigDecimal((double) -123.456));
		_testBigDecimal(new BigDecimal((double) 0.123456789));
		_testBigDecimal(new BigDecimal((double) -0.123456789));
		_testBigDecimal(new BigDecimal(Double.MAX_VALUE));
		_testBigDecimal(new BigDecimal(Double.MIN_VALUE));
	}

	static void _testBigDecimal(BigDecimal src) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Template tmpl = BigDecimalTemplate.getInstance();
		tmpl.pack(new Packer(out), src);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		BigDecimal dst = (BigDecimal) tmpl.unpack(new Unpacker(in), null);
		assertEquals(src, dst);
	}

	@Test
	public void testNullBigDecimal() throws Exception {
		BigDecimal src = null;
		Template tmpl = BigDecimalTemplate.getInstance();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		Packer packer = new Packer(out);
		try {
			tmpl.pack(packer, src);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		packer.pack(src);
		byte[] bytes = out.toByteArray();
		Unpacker unpacker = new Unpacker();
		try {
			unpacker.wrap(bytes);
			tmpl.unpack(unpacker, null);
			fail();
		} catch (Exception e) {
			assertTrue(e instanceof MessageTypeException);
		}
		unpacker.wrap(bytes);
		tmpl = new NullableTemplate(BigDecimalTemplate.getInstance());
		BigDecimal dst = (BigDecimal) tmpl.unpack(unpacker, null);
		assertEquals(src, dst);
	}
}
