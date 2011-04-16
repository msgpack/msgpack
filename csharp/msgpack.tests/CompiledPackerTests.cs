using System;
using System.Collections.Generic;
using NUnit.Framework;
using TestA_Class = msgpack.tests.ObjectPackerTests.TestA_Class;
using TestB_Class = msgpack.tests.ObjectPackerTests.TestB_Class;

namespace msgpack.tests
{
	[TestFixture]
	public class CompiledPackerTests
	{
		[Test]
		public void TestA ()
		{
			TestA_Class obj0 = new TestA_Class ();
			TestA_Class obj1 = CompiledPacker.Unpack<TestA_Class> (CompiledPacker.Pack<TestA_Class> (obj0));
			obj0.Check (obj1);
		}

		[Test]
		public void TestB ()
		{
			TestB_Class obj0 = TestB_Class.Create ();
			TestB_Class obj1 = CompiledPacker.Unpack<TestB_Class> (CompiledPacker.Pack<TestB_Class> (obj0));
			obj0.Check (obj1);
		}
	}
}
