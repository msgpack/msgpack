using System;
using System.Collections.Generic;
using NUnit.Framework;

namespace MsgPack.Test
{
    [TestFixture]
    public abstract class DataTypesTestsBase
    {
        protected IMsgPacker _packer;

        [Test]
        public void Unpack_NullString()
        {
            var buf = new byte[] {0xa0};
            var res = _packer.Unpack<string>(buf);
            Assert.IsNotNull(res);
            Assert.AreEqual(0,res.Length);
        }

        [Test]
        public void Unpack_EmptyString()
        {
            var buf = new byte[] { 0xc0 };
            var res = _packer.Unpack<string>(buf);
            Assert.IsNull(res);
        }

        [Test]
        public void Pack_Guid()
        {
            var obj = new TestGuid {MyGuid = Guid.Empty};

            var res = _packer.Pack(obj);

            Assert.AreEqual(new byte[] {
            0x81, // Map length 1
                0xa6, // Raw length 6
                     0x4d,0x79,0x47,0x75,0x69,0x64, // MyGuid
                0xda,0x00,0x20, // Raw length 32
                     48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,
                     48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48// Guid.Empty
            }, res);
        }

        [Test]
        public void UnPack_Guid()
        {
            var buf = new byte[] {
            0x81, // Map length 1
                0xa6, // Raw length 6
                     0x4d,0x79,0x47,0x75,0x69,0x64, // MyGuid
                0xda,0x00,0x20, // Raw length 32
                     48,49,48,50,48,51,48,52,48,48,48,48,48,48,48,48,
                     48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48// Guid.Empty
            };

            var res = _packer.Unpack<TestGuid>(buf);

            Assert.AreEqual(Guid.Parse("01020304000000000000000000000000"), res.MyGuid);
        }

        [Test]
        public void UnPack_EmptyGuid()
        {
            var buf = new byte[] {
            0x81, // Map length 1
                0xa6, // Raw length 6
                     0x4d,0x79,0x47,0x75,0x69,0x64, // MyGuid
                0xa0 // Raw length 0
            };

            var res = _packer.Unpack<TestGuid>(buf);

            Assert.AreEqual(Guid.Empty, res.MyGuid);
        }

        [Test]
        public void UnPack_NullGuid()
        {
            var buf = new byte[] {
            0x81, // Map length 1
                0xa6, // Raw length 6
                     0x4d,0x79,0x47,0x75,0x69,0x64, // MyGuid
                0xc0 // Raw length 0
            };

            var res = _packer.Unpack<TestGuid>(buf);

            Assert.AreEqual(Guid.Empty, res.MyGuid);
        }


        [Test]
        public void Pack_Dictionary_WorksAsMap()
        {
            var dict = new Dictionary<string, string> { { "a", "b" }, { "c", "d" } };

            var res = _packer.Pack<Dictionary<string, string>>(dict);

            Assert.AreEqual(new byte[] { 130, 161, 97, 161, 98, 161, 99, 161, 100 }, res);
        }

        [Test]
        public void Pack_DictionaryInDictionary_WorksAsMap()
        {
            var dict = new Dictionary<string, Dictionary<string, string>> { { "a", new Dictionary<string, string> { { "b", "c" } } } };

            var res = _packer.Pack<Dictionary<string, Dictionary<string, string>>>(dict);

            Assert.AreEqual(new byte[] { 129, 161, 97, 129, 161, 98, 161, 99 }, res);
        }

        [Test]
        public void UnPack_EmptyDictionary()
        {
            var testData = new byte[] {0x80};
            var res = _packer.Unpack<Dictionary<string,int>>(testData);
            Assert.IsNotNull(res);
            Assert.IsEmpty(res);
        }

        [Test]
        public void UnPack_DictionaryInAClass()
        {
            var testData = new byte[] { 0x81, 0xa2, 0x4d,0x64,0x80  };
            var res = _packer.Unpack<TestDictionary1>(testData);
            Assert.IsNotNull(res);
        }

        [Test,Ignore]
        public void Pack_AChar()
        {
            char myChar = 'a';
            var res = _packer.Pack<char>(myChar);

            Assert.AreEqual(new byte[] { 97 }, res);
        }

        [Test]
        public void Pack_AChar_InAClass()
        {
            var myChar = new TestChar {MyChar = 'a'};
            var res = _packer.Pack<TestChar>(myChar);

            Assert.AreEqual(new byte[] { 129 // map size 1
                , 166 // raw size 6
                , 77, 121, 67, 104, 97, 114, // the string "MyChar"
                97 // int 0-127
            }, res);
        }

        #region Test Box classes
        public class TestGuid
        {
            public Guid MyGuid { get; set; }
        }

        public class TestChar
        {
            public char MyChar { get; set; }
        }

        public class TestDictionary1
        {
            public Dictionary<string,int> Md { get; set; }
        }
        #endregion
    }
}
