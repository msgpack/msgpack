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
		CompiledPacker _mbImpl = new CompiledPacker (false);
		CompiledPacker _dynImpl = new CompiledPacker (true);

		[Test]
		public void TestA_MethodBuilder ()
		{
			TestA (_mbImpl);
		}

		[Test]
		public void TestA_DynamicMethod ()
		{
			TestA (_dynImpl);
		}

		[Test]
		public void TestB_MethodBuilder ()
		{
			TestB (_mbImpl);
		}

		[Test]
		public void TestB_DynamicMethod ()
		{
			TestB (_dynImpl);
		}

		void TestA (CompiledPacker packer)
		{
			TestA_Class obj0 = new TestA_Class ();
			TestA_Class obj1 = packer.Unpack<TestA_Class> (packer.Pack<TestA_Class> (obj0));
			obj0.Check (obj1);
		}

		void TestB (CompiledPacker packer)
		{
			TestB_Class obj0 = TestB_Class.Create ();
			TestB_Class obj1 = packer.Unpack<TestB_Class> (packer.Pack<TestB_Class> (obj0));
			obj0.Check (obj1);
		}
	}
}
