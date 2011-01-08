package org.msgpack;

import org.msgpack.*;
import org.msgpack.object.*;
import org.msgpack.annotation.*;
import static org.msgpack.Templates.*;

import java.io.*;
import java.util.*;
import java.math.BigInteger;

import org.junit.Test;
import junit.framework.TestCase;

public class TestArrays extends TestCase {
	@MessagePackMessage
	public static class PrimitiveTest {
		public PrimitiveTest() { }
		public boolean[] b = new boolean[0];
		public short[] s = new short[0];
		public int[] i = new int[0];
		//public long[] l = new long[0];  // FIXME javassist?
		public float[] f = new float[0];
		//public double[] d = new double[0];  // FIXME javassist?
	}

	@Test
	public void testPrimitive() {
		PrimitiveTest t = new PrimitiveTest();
		t.b = new boolean[] {true, false};
		t.s = new short[] {0, 1};
		t.i = new int[] {2, 3};
		//t.l = new long[] {4, 5};
		t.f = new float[] {2.0f, 4.0f};
		//t.d = new double[] {8.0, 16.0};

		byte[] raw = MessagePack.pack(t);

		PrimitiveTest u = MessagePack.unpack(raw, PrimitiveTest.class);
		assertEquals(t.b.length, u.b.length);
		for(int i=0; i < t.b.length; i++) { assertEquals(t.b[i], u.b[i]); }
		assertEquals(t.s.length, u.s.length);
		for(int i=0; i < t.s.length; i++) { assertEquals(t.s[i], u.s[i]); }
		assertEquals(t.i.length, u.i.length);
		for(int i=0; i < t.i.length; i++) { assertEquals(t.i[i], u.i[i]); }
		//assertEquals(t.l.length, u.l.length);
		//for(int i=0; i < t.l.length; i++) { assertEquals(t.l[i], u.l[i]); }
		assertEquals(t.f.length, u.f.length);
		for(int i=0; i < t.f.length; i++) { assertEquals(t.f[i], u.f[i]); }
		//assertEquals(t.d.length, u.d.length);
		//for(int i=0; i < t.d.length; i++) { assertEquals(t.d[i], u.d[i]); }

		PrimitiveTest c = MessagePack.unpack(raw).convert(PrimitiveTest.class);
		assertEquals(t.b.length, c.b.length);
		for(int i=0; i < t.b.length; i++) { assertEquals(t.b[i], c.b[i]); }
		assertEquals(t.s.length, c.s.length);
		for(int i=0; i < t.s.length; i++) { assertEquals(t.s[i], c.s[i]); }
		assertEquals(t.i.length, c.i.length);
		for(int i=0; i < t.i.length; i++) { assertEquals(t.i[i], c.i[i]); }
		//assertEquals(t.l.length, c.l.length);
		//for(int i=0; i < t.l.length; i++) { assertEquals(t.l[i], c.l[i]); }
		assertEquals(t.f.length, c.f.length);
		for(int i=0; i < t.f.length; i++) { assertEquals(t.f[i], c.f[i]); }
		//assertEquals(t.d.length, c.d.length);
		//for(int i=0; i < t.d.length; i++) { assertEquals(t.d[i], c.d[i]); }
	}

	@MessagePackMessage
	public static class ReferenceTest {
		public ReferenceTest() { }
		public Boolean[] b;
		public Short[] s;
		public Integer[] i;
		public Long[] l;
		public Float[] f;
		public Double[] d;
		public String[] str;
	}

	@Test
	public void testReference() {
		ReferenceTest t = new ReferenceTest();
		t.b = new Boolean[] {true, false};
		t.s = new Short[] {0, 1};
		t.i = new Integer[] {2, 3};
		t.l = new Long[] {4l, 5l};
		t.f = new Float[] {2.0f, 4.0f};
		t.d = new Double[] {8.0, 16.0};
		t.str = new String[] {"furuhashi", "java"};

		byte[] raw = MessagePack.pack(t);

		ReferenceTest u = MessagePack.unpack(raw, ReferenceTest.class);
		assertEquals(t.b.length, u.b.length);
		for(int i=0; i < t.b.length; i++) { assertEquals(t.b[i], u.b[i]); }
		assertEquals(t.s.length, u.s.length);
		for(int i=0; i < t.s.length; i++) { assertEquals(t.s[i], u.s[i]); }
		assertEquals(t.i.length, u.i.length);
		for(int i=0; i < t.i.length; i++) { assertEquals(t.i[i], u.i[i]); }
		assertEquals(t.l.length, u.l.length);
		for(int i=0; i < t.l.length; i++) { assertEquals(t.l[i], u.l[i]); }
		assertEquals(t.f.length, u.f.length);
		for(int i=0; i < t.f.length; i++) { assertEquals(t.f[i], u.f[i]); }
		assertEquals(t.d.length, u.d.length);
		for(int i=0; i < t.d.length; i++) { assertEquals(t.d[i], u.d[i]); }
		assertEquals(t.str.length, u.str.length);
		for(int i=0; i < t.str.length; i++) { assertEquals(t.str[i], u.str[i]); }

		ReferenceTest c = MessagePack.unpack(raw).convert(ReferenceTest.class);
		assertEquals(t.b.length, c.b.length);
		for(int i=0; i < t.b.length; i++) { assertEquals(t.b[i], c.b[i]); }
		assertEquals(t.s.length, c.s.length);
		for(int i=0; i < t.s.length; i++) { assertEquals(t.s[i], c.s[i]); }
		assertEquals(t.i.length, c.i.length);
		for(int i=0; i < t.i.length; i++) { assertEquals(t.i[i], c.i[i]); }
		assertEquals(t.l.length, c.l.length);
		for(int i=0; i < t.l.length; i++) { assertEquals(t.l[i], c.l[i]); }
		assertEquals(t.f.length, c.f.length);
		for(int i=0; i < t.f.length; i++) { assertEquals(t.f[i], c.f[i]); }
		assertEquals(t.d.length, c.d.length);
		for(int i=0; i < t.d.length; i++) { assertEquals(t.d[i], c.d[i]); }
		assertEquals(t.str.length, c.str.length);
		for(int i=0; i < t.str.length; i++) { assertEquals(t.str[i], c.str[i]); }
	}

	@MessagePackMessage
	public static class GenericsTest {
		public GenericsTest() { }
		public List<String>[] slist;
		public Map<String, Integer>[] imap;
	}

	@Test
	public void testGenerics() {
		GenericsTest t = new GenericsTest();
		t.slist = new List[2];
		t.slist[0] = new ArrayList();
		t.slist[0].add("aa");
		t.slist[0].add("bb");
		t.slist[1] = new ArrayList();
		t.slist[1].add("cc");
		t.imap = new Map[2];
		t.imap[0] = new HashMap();
		t.imap[0].put("aa", 1);
		t.imap[0].put("bb", 2);
		t.imap[1] = new HashMap();
		t.imap[1].put("cc", 3);

		byte[] raw = MessagePack.pack(t);

		GenericsTest u = MessagePack.unpack(raw, GenericsTest.class);
		assertEquals(t.slist.length, u.slist.length);
		for(int i=0; i < t.slist.length; i++) {
			assertEquals(t.slist[i].size(), u.slist[i].size());
			for(int j=0; j < t.slist[i].size(); j++) {
				assertEquals(t.slist[i].get(j), u.slist[i].get(j));
			}
		}
		for(int i=0; i < t.imap.length; i++) {
			assertEquals(t.imap[i].size(), u.imap[i].size());
			for(String j : t.imap[i].keySet()) {
				assertEquals(t.imap[i].get(j), u.imap[i].get(j));
			}
		}

		GenericsTest c = MessagePack.unpack(raw).convert(GenericsTest.class);
		assertEquals(t.slist.length, c.slist.length);
		for(int i=0; i < t.slist.length; i++) {
			assertEquals(t.slist[i].size(), c.slist[i].size());
			for(int j=0; j < t.slist[i].size(); j++) {
				assertEquals(t.slist[i].get(j), c.slist[i].get(j));
			}
		}
		for(int i=0; i < t.imap.length; i++) {
			assertEquals(t.imap[i].size(), c.imap[i].size());
			for(String j : t.imap[i].keySet()) {
				assertEquals(t.imap[i].get(j), c.imap[i].get(j));
			}
		}
	}

	@MessagePackMessage
	public static class Dim2Test {
		public Dim2Test() { }
		public int[][] i;
		public String[][] str;
		public List<String>[][] slist;
	}

	@Test
	public void testDim2() {
		Dim2Test t = new Dim2Test();
		t.i = new int[2][];
		t.i[0] = new int[] {0, 1};
		t.i[1] = new int[] {2, 3, 4};
		t.str = new String[2][];
		t.str[0] = new String[] {"aa", "bb"};
		t.str[1] = new String[] {"cc", "dd", "ee"};
		t.slist = new List[2][];
		t.slist[0] = new List[1];
		t.slist[0][0] = new ArrayList();
		t.slist[0][0].add("ff");
		t.slist[0][0].add("gg");
		t.slist[1] = new List[2];
		t.slist[1][0] = new ArrayList();
		t.slist[1][0].add("hh");
		t.slist[1][0].add("ii");
		t.slist[1][1] = new ArrayList();
		t.slist[1][1].add("jj");
		t.slist[1][1].add("kk");

		byte[] raw = MessagePack.pack(t);

		Dim2Test u = MessagePack.unpack(raw, Dim2Test.class);
		assertEquals(t.i.length, t.i.length);
		for(int i=0; i < t.i.length; i++) {
			assertEquals(t.i[i].length, u.i[i].length);
			for(int j=0; j < t.i[i].length; j++) {
				assertEquals(t.i[i][j], u.i[i][j]);
			}
		}
		assertEquals(t.str.length, t.str.length);
		for(int i=0; i < t.str.length; i++) {
			assertEquals(t.str[i].length, u.str[i].length);
			for(int j=0; j < t.str[i].length; j++) {
				assertEquals(t.str[i][j], u.str[i][j]);
			}
		}
		assertEquals(t.slist.length, t.slist.length);
		for(int i=0; i < t.slist.length; i++) {
			assertEquals(t.slist[i].length, u.slist[i].length);
			for(int j=0; j < t.slist[i].length; j++) {
				assertEquals(t.slist[i][j].size(), u.slist[i][j].size());
				for(int k=0; k < t.slist[i][j].size(); k++) {
					assertEquals(t.slist[i][j].get(k), u.slist[i][j].get(k));
				}
			}
		}
	}

	@MessagePackMessage
	public static class Dim3Test {
		public Dim3Test() { }
		public int[][][] i;
		public String[][][] str;
		public List<String>[][][] slist;
	}

	@Test
	public void testDim3() {
		Dim3Test t = new Dim3Test();
		t.i = new int[2][][];
		t.i[0] = new int[2][];
		t.i[0][0] = new int[] {0, 1};
		t.i[0][1] = new int[] {2, 3, 4};
		t.i[1] = new int[1][];
		t.i[1][0] = new int[] {5};
		t.str = new String[2][][];
		t.str[0] = new String[1][];
		t.str[0][0] = new String[] {"aa", "bb"};
		t.str[1] = new String[2][];
		t.str[1][0] = new String[] {"cc", "dd", "ee"};
		t.str[1][1] = new String[] {"ff"};
		t.slist = new List[2][][];
		t.slist[0] = new List[2][];
		t.slist[0][0] = new List[1];
		t.slist[0][0][0] = new ArrayList();
		t.slist[0][0][0].add("ff");
		t.slist[0][0][0].add("gg");
		t.slist[0][1] = new List[2];
		t.slist[0][1][0] = new ArrayList();
		t.slist[0][1][0].add("hh");
		t.slist[0][1][0].add("ii");
		t.slist[0][1][1] = new ArrayList();
		t.slist[0][1][1].add("jj");
		t.slist[0][1][1].add("kk");
		t.slist[1] = new List[1][];
		t.slist[1][0] = new List[0];

		byte[] raw = MessagePack.pack(t);

		Dim3Test u = MessagePack.unpack(raw, Dim3Test.class);
		assertEquals(t.i.length, t.i.length);
		for(int i=0; i < t.i.length; i++) {
			assertEquals(t.i[i].length, u.i[i].length);
			for(int j=0; j < t.i[i].length; j++) {
				for(int k=0; k < t.i[i].length; k++) {
					assertEquals(t.i[i][j][k], u.i[i][j][k]);
				}
			}
		}
		assertEquals(t.str.length, t.str.length);
		for(int i=0; i < t.str.length; i++) {
			assertEquals(t.str[i].length, u.str[i].length);
			for(int j=0; j < t.str[i].length; j++) {
				assertEquals(t.str[i][j].length, u.str[i][j].length);
				for(int k=0; k < t.str[i][j].length; k++) {
					assertEquals(t.str[i][j][k], u.str[i][j][k]);
				}
			}
		}
		assertEquals(t.slist.length, t.slist.length);
		for(int i=0; i < t.slist.length; i++) {
			assertEquals(t.slist[i].length, u.slist[i].length);
			for(int j=0; j < t.slist[i].length; j++) {
				assertEquals(t.slist[i][j].length, u.slist[i][j].length);
				for(int k=0; k < t.slist[i][j].length; k++) {
					assertEquals(t.slist[i][j][k].size(), u.slist[i][j][k].size());
					for(int l=0; l < t.slist[i][j][k].size(); l++) {
						assertEquals(t.slist[i][j][k].get(l), u.slist[i][j][k].get(l));
					}
				}
			}
		}
	}

	@Test
	public void testLocal() throws IOException {
		int[][][] src = new int[10][20][30];
		for (int i = 0; i < 10; ++i) {
			for (int j = 0; j < 20; ++j) {
				for (int k = 0; k < 30; ++k) {
					src[i][j][k] = (int) (Math.random() * 100);
				}
			}
		}

		byte[] raw = MessagePack.pack(src);

		int[][][] u = MessagePack.unpack(raw, int[][][].class);
		assertEquals(src.length, u.length);
		for(int i = 0; i < src.length; ++i) {
			assertEquals(src[i].length, u[i].length);
			for(int j = 0; j < src[i].length; ++j) {
				assertEquals(src[i][j].length, u[i][j].length);
				for(int k = 0; k < src[i][j].length; ++k) {
					assertEquals(src[i][j][k], u[i][j][k]);
				}
			}
		}

		int[][][] c = MessagePack.unpack(raw).convert(int[][][].class);
		assertEquals(src.length, c.length);
		for(int i = 0; i < src.length; ++i) {
			assertEquals(src[i].length, c[i].length);
			for(int j = 0; j < src[i].length; ++j) {
				assertEquals(src[i][j].length, c[i][j].length);
				for(int k = 0; k < src[i][j].length; ++k) {
					assertEquals(src[i][j][k], c[i][j][k]);
				}
			}
		}
	}
}

