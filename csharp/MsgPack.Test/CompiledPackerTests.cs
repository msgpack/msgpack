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
using System.Collections.Generic;
using NUnit.Framework;
using TestA_Class = MsgPack.Test.ObjectPackerTests.TestA_Class;
using TestB_Class = MsgPack.Test.ObjectPackerTests.TestB_Class;

namespace MsgPack.Test
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

        [Test]
        public void Dictionary_WorksAsMap()
        {
            var dict = new Dictionary<string, string> { { "a", "b" }, { "c", "d" } };

            var res = _dynImpl.Pack<Dictionary<string, string>>(dict);

            Assert.AreEqual(new byte[]{130,161,97,161,98,161,99,161,100},res);
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
