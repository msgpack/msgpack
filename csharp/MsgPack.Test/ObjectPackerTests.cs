//
// Copyright 2011 Kazuki Oikawa
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

using System;
using NUnit.Framework;

namespace MsgPack.Test
{
	[TestFixture]
	public class ObjectPackerTests
	{
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
			TestB_Class obj0 = TestB_Class.Create ();
			TestB_Class obj1 = packer.Unpack<TestB_Class> (packer.Pack (obj0));
			obj0.Check (obj1);
		}

		public class TestA_Class
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

		public class TestB_Class
		{
			public TestA_Class x;
			public TestB_Class nested;
			public int[] list;

			public static TestB_Class Create ()
			{
				return Create (0);
			}

			static TestB_Class Create (int level)
			{
				TestB_Class obj = new TestB_Class ();
				obj.x = new TestA_Class ();
				if (level < 10)
					obj.nested = Create (level + 1);
				if ((level % 2) == 0)
					obj.list = new int[] {level, 0, level, int.MaxValue, level};
				return obj;
			}

			public void Check (TestB_Class other)
			{
				x.Check (other.x);
				if (nested != null)
					nested.Check (other.nested);
				Assert.AreEqual (list, other.list);
			}
		}
	}
}
