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


using NUnit.Framework;

namespace MsgPack.Test
{
    [TestFixture]
    public class CompiledPackerMethodBuilderTests : DataTypesTestsBase
    {
        [TestFixtureSetUp]
        public void SetUpFixture()
        {
            _packer = new CompiledPacker(false);
        }

        [Test]
        public void TwoPackers_SameType_DoNotConflict()
        {
            var packerA = new CompiledPacker(false);
            var packerB = new CompiledPacker(false);
            var item = new TestTwoPackers {Test = "TestString"};

            packerA.Pack(item);
            packerB.Pack(item);
        }

        public class TestTwoPackers
        {
            public string Test;
        }
    }
}
