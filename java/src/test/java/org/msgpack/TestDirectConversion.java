package org.msgpack;

import org.msgpack.*;
import java.io.*;
import java.util.*;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestDirectConversion {
	@Test
	public void testInt() throws Exception {
		testInt(0);
		testInt(-1);
		testInt(1);
		testInt(Integer.MIN_VALUE);
		testInt(Integer.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++)
			testInt(rand.nextInt());
	}
	public void testInt(int val) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(val);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		assertEquals(val, pac.unpackInt());
	}

	@Test
	public void testLong() throws Exception {
		testLong(0);
		testLong(-1);
		testLong(1);
		testLong(Integer.MIN_VALUE);
		testLong(Integer.MAX_VALUE);
		testLong(Long.MIN_VALUE);
		testLong(Long.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++)
			testLong(rand.nextLong());
	}
	public void testLong(long val) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(val);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		assertEquals(val, pac.unpackLong());
	}

	@Test
	public void testFloat() throws Exception {
		testFloat((float)0.0);
		testFloat((float)-0.0);
		testFloat((float)1.0);
		testFloat((float)-1.0);
		testFloat((float)Float.MAX_VALUE);
		testFloat((float)Float.MIN_VALUE);
		testFloat((float)Float.NaN);
		testFloat((float)Float.NEGATIVE_INFINITY);
		testFloat((float)Float.POSITIVE_INFINITY);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++)
			testFloat(rand.nextFloat());
	}
	public void testFloat(float val) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(val);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		assertEquals(val, pac.unpackFloat(), 10e-10);
	}

	@Test
	public void testDouble() throws Exception {
		testDouble((double)0.0);
		testDouble((double)-0.0);
		testDouble((double)1.0);
		testDouble((double)-1.0);
		testDouble((double)Double.MAX_VALUE);
		testDouble((double)Double.MIN_VALUE);
		testDouble((double)Double.NaN);
		testDouble((double)Double.NEGATIVE_INFINITY);
		testDouble((double)Double.POSITIVE_INFINITY);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++)
			testDouble(rand.nextDouble());
	}
	public void testDouble(double val) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(val);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		assertEquals(val, pac.unpackDouble(), 10e-10);
	}

	@Test
	public void testNil() throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).packNil();
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		assertEquals(null, pac.unpackNull());
	}

	@Test
	public void testBoolean() throws Exception {
		testBoolean(false);
		testBoolean(true);
	}
	public void testBoolean(boolean val) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(val);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		assertEquals(val, pac.unpackBoolean());
	}

	@Test
	public void testString() throws Exception {
		testString("");
		testString("a");
		testString("ab");
		testString("abc");

		// small size string
		for (int i = 0; i < 100; i++) {
			StringBuilder sb = new StringBuilder();
			int len = (int)Math.random() % 31 + 1;
			for (int j = 0; j < len; j++)
				sb.append('a' + ((int)Math.random()) & 26);
			testString(sb.toString());
		}

		// medium size string
		for (int i = 0; i < 100; i++) {
			StringBuilder sb = new StringBuilder();
			int len = (int)Math.random() % 100 + (1 << 15);
			for (int j = 0; j < len; j++)
				sb.append('a' + ((int)Math.random()) & 26);
			testString(sb.toString());
		}

		// large size string
		for (int i = 0; i < 10; i++) {
			StringBuilder sb = new StringBuilder();
			int len = (int)Math.random() % 100 + (1 << 31);
			for (int j = 0; j < len; j++)
				sb.append('a' + ((int)Math.random()) & 26);
			testString(sb.toString());
		}
	}
	public void testString(String val) throws Exception {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		new Packer(out).pack(val);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		assertEquals(val, pac.unpackString());
	}

	@Test
	public void testArray() throws Exception {
		List<Integer> emptyList = new ArrayList<Integer>();
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(emptyList);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Unpacker pac = new Unpacker(in);
			int ulen = pac.unpackArray();
			assertEquals(0, ulen);
		}

		for (int i = 0; i < 1000; i++) {
			List<Integer> l = new ArrayList<Integer>();
			int len = (int)Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++)
				l.add(j);
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(l);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Unpacker pac = new Unpacker(in);
			int ulen = pac.unpackArray();
			assertEquals(len, ulen);
			for (int j = 0; j < len; j++) {
				assertEquals(l.get(j).intValue(), pac.unpackInt());
			}
		}

		for (int i = 0; i < 1000; i++) {
			List<String> l = new ArrayList<String>();
			int len = (int)Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++)
				l.add(Integer.toString(j));
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(l);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Unpacker pac = new Unpacker(in);
			int ulen = pac.unpackArray();
			assertEquals(len, ulen);
			for (int j = 0; j < len; j++) {
				assertEquals(l.get(j), pac.unpackString());
			}
		}
	}

	@Test
	public void testMap() throws Exception {
		Map<Integer, Integer> emptyMap = new HashMap<Integer, Integer>();
		{
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(emptyMap);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Unpacker pac = new Unpacker(in);
			int ulen = pac.unpackMap();
			assertEquals(0, ulen);
		}

		for (int i = 0; i < 1000; i++) {
			Map<Integer, Integer> m = new HashMap<Integer, Integer>();
			int len = (int)Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++)
				m.put(j, j);
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(m);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Unpacker pac = new Unpacker(in);
			int ulen = pac.unpackMap();
			assertEquals(len, ulen);
			for (int j = 0; j < len; j++) {
				Integer val = m.get(pac.unpackInt());
				assertNotNull(val);
				assertEquals(val.intValue(), pac.unpackInt());
			}
		}

		for (int i = 0; i < 1000; i++) {
			Map<String, Integer> m = new HashMap<String, Integer>();
			int len = (int)Math.random() % 1000 + 1;
			for (int j = 0; j < len; j++)
				m.put(Integer.toString(j), j);
			ByteArrayOutputStream out = new ByteArrayOutputStream();
			new Packer(out).pack(m);
			ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
			Unpacker pac = new Unpacker(in);
			int ulen = pac.unpackMap();
			assertEquals(len, ulen);
			for (int j = 0; j < len; j++) {
				Integer val = m.get(pac.unpackString());
				assertNotNull(val);
				assertEquals(val.intValue(), pac.unpackInt());
			}
		}
	}
};

