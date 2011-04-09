using System;
using System.Collections.Generic;
using System.Linq;
using NUnit.Framework;

namespace msgpack.tests
{
	[TestFixture]
	public class BoxingPackerTests
	{
		[Test]
		public void NullTest ()
		{
			BoxingPacker packer = new BoxingPacker ();
			Assert.IsNull (packer.Unpack (packer.Pack (null)));
		}

		[Test]
		public void PrimitiveTypeTest ()
		{
			BoxingPacker packer = new BoxingPacker ();
			RoundtripTest<int> (packer, 12345);
			RoundtripTest<ulong> (packer, 1234567890123456789UL);
			RoundtripTest<double> (packer, Math.PI);
			RoundtripTest<bool> (packer, true);
			RoundtripTest<bool> (packer, false);
		}

		[Test]
		public void ArrayTest ()
		{
			BoxingPacker packer = new BoxingPacker ();
			RoundtripTest<object[]> (packer, new object[0]);
			RoundtripTest<object[]> (packer, new object[]{
				int.MinValue, int.MaxValue, 1234567890123456789UL, ulong.MaxValue,
				float.MinValue, float.MaxValue, float.Epsilon, float.NaN, float.PositiveInfinity, float.NegativeInfinity,
				double.MinValue, double.MaxValue, double.Epsilon, double.NaN, double.PositiveInfinity, double.NegativeInfinity,
				null, true, false, new object[] {
					new object[] {1, 2, 3},
					new object[] {Math.PI, true}
				}
			});
		}

		[Test]
		public void MapTest ()
		{
			BoxingPacker packer = new BoxingPacker ();
			Dictionary<object, object> dic = new Dictionary<object,object> ();
			Dictionary<object, object> dic2 = new Dictionary<object,object> ();
			RoundtripTest<IDictionary<object,object>> (packer, dic);

			dic2.Add (123, 456);
			dic2.Add (234, 567);
			dic2.Add (345, 678);

			dic.Add (0, 0.123);
			dic.Add (Math.PI, true);
			dic.Add (false, new object[] {1, 2, 3});
			dic.Add (1, new Dictionary<object,object> (dic2));
			RoundtripTest<IDictionary<object,object>> (packer, dic);

			dic[1] = ((Dictionary<object,object>)dic[1]).ToArray ();
			Assert.AreEqual (dic, packer.Unpack (packer.Pack (dic.ToArray ())));
		}

		void RoundtripTest<T> (BoxingPacker packer, T obj)
		{
			T obj2 = (T)packer.Unpack (packer.Pack (obj));
			Assert.AreEqual (obj, obj2);
		}
	}
}
