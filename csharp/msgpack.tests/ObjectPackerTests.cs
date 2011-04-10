using System;
using System.Collections.Generic;
using NUnit.Framework;

namespace msgpack.tests
{
	[TestFixture]
	public class ObjectPackerTests
	{
		public static void Main ()
		{
			ObjectPackerTests tests = new ObjectPackerTests ();
			tests.TestA ();
		}

		[Test]
		public void TestA ()
		{
			ObjectPacker packer = new ObjectPacker ();
			TestA_Class obj0 = new TestA_Class ();
			TestA_Class obj1 = packer.Unpack<TestA_Class> (packer.Pack (obj0));
			obj0.Check (obj1);
		}

		[Test]
		public void TestB ()
		{
			ObjectPacker packer = new ObjectPacker ();
			Dictionary<int, int> dic = new Dictionary<int,int> ();
			Random rnd = new Random ();
			int size = rnd.Next () & 0xff;
			for (int i = 0; i < size; i ++)
				dic[rnd.Next()] = rnd.Next ();
			Dictionary<int, int> dic_ = packer.Unpack<Dictionary<int, int>> (packer.Pack (dic));
			Assert.AreEqual (dic, dic_);
		}

		class TestA_Class
		{
			public bool a;
			public byte b;
			public sbyte c;
			public short d;
			public ushort e;
			public int f;
			public uint g;
			public long h;
			public ulong i;
			public float j;
			public double k;
			public int[] l;
			public string m;

			public TestA_Class ()
			{
				Random rnd = new Random ();
				a = rnd.NextDouble () < 0.5;
				b = (byte)rnd.Next ();
				c = (sbyte)rnd.Next ();
				d = (short)rnd.Next ();
				e = (ushort)rnd.Next ();
				f = (int)rnd.Next ();
				g = (uint)rnd.Next ();
				h = (long)rnd.Next ();
				i = (ulong)rnd.Next ();
				j = (float)rnd.NextDouble ();
				k = (double)rnd.NextDouble ();
				l = new int[rnd.Next () & 0xff];
				for (int z = 0; z < l.Length; z ++)
					l[z] = rnd.Next ();

				byte[] buf = new byte[rnd.Next() & 0xff];
				rnd.NextBytes (buf);
				m = Convert.ToBase64String (buf);
			}
			
			public void Check (TestA_Class other)
			{
				Assert.AreEqual (this.a, other.a);
				Assert.AreEqual (this.b, other.b);
				Assert.AreEqual (this.c, other.c);
				Assert.AreEqual (this.d, other.d);
				Assert.AreEqual (this.e, other.e);
				Assert.AreEqual (this.f, other.f);
				Assert.AreEqual (this.g, other.g);
				Assert.AreEqual (this.h, other.h);
				Assert.AreEqual (this.i, other.i);
				Assert.AreEqual (this.j, other.j);
				Assert.AreEqual (this.k, other.k);
				Assert.AreEqual (this.l, other.l);
				Assert.AreEqual (this.m, other.m);
			}
		}
	}
}
