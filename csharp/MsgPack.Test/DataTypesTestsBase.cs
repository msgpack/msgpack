using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using NUnit.Framework;

namespace MsgPack.Test
{
    [TestFixture]
    public abstract class DataTypesTestsBase
    {
        protected IMsgPacker _packer;

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
        #endregion
    }
}
