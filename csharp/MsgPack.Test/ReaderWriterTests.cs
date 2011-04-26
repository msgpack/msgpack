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
using System.IO;
using NUnit.Framework;

namespace MsgPack.Test
{
	[TestFixture]
	public class ReaderWriterTests
	{
		[Test]
		public void SignedNumberTest ()
		{
			long[] nums = new long[]{
				/* positive fixnum */
				0, 1, 126, 127,
				
				/* negative fixnum */
				-1, -2, -31, -32,

				/* int8 */
				-128, -33,

				/* int16 */
				-32768, -129, 128, 32767,

				/* int32 */
				-2147483648, -32769, 32768, 2147483647,

				/* int64 */
				-9223372036854775808, -2147483649, 2147483648, 9223372036854775807
			};
			byte[] expectedBytes = new byte[] {
				/* positive fixnum */
				0, 1, 126, 127,
				
				/* negative fixnum */
				0xff, 0xfe, 0xe1, 0xe0,

				/* int8 */
				0xd0, 0x80,
				0xd0, 0xdf,

				/* int16 */
				0xd1, 0x80, 0x00,
				0xd1, 0xff, 0x7f,
				0xd1, 0x00, 0x80,
				0xd1, 0x7f, 0xff,

				/* int32 */
				0xd2, 0x80, 0x00, 0x00, 0x00,
				0xd2, 0xff, 0xff, 0x7f, 0xff,
				0xd2, 0x00, 0x00, 0x80, 0x00,
				0xd2, 0x7f, 0xff, 0xff, 0xff,

				/* int64 */
				0xd3, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
				0xd3, 0xff, 0xff, 0xff, 0xff, 0x7f, 0xff, 0xff, 0xff,
				0xd3, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00,
				0xd3, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
			};

			Test (delegate (MsgPackWriter writer) {
				for (int i = 0; i < nums.Length; i ++) {
					writer.Write (nums[i]);
				}
			}, delegate (MsgPackReader reader) {
				for (int i = 0; i < nums.Length; i ++) {
					Assert.IsTrue (reader.Read ());
					Assert.IsTrue (reader.IsSigned () || reader.IsSigned64 ());
					if (reader.IsSigned64 ()) {
						Assert.AreEqual (nums[i], reader.ValueSigned64);
					} else {
						Assert.AreEqual (nums[i], reader.ValueSigned);
					}
				}
			}, expectedBytes);
		}

		[Test]
		public void UnsignedNumberTest ()
		{
			ulong[] nums = new ulong[]{
				/* uint8 */
				128, byte.MaxValue,

				/* uint16 */
				byte.MaxValue + 1, ushort.MaxValue,

				/* uint32 */
				ushort.MaxValue + 1U, uint.MaxValue,

				/* uint64 */
				uint.MaxValue + 1UL, ulong.MaxValue
			};
			byte[] expectedBytes = new byte[] {
				/* int8 */
				0xcc, 0x80,
				0xcc, 0xff,

				/* int16 */
				0xcd, 0x01, 0x00,
				0xcd, 0xff, 0xff,

				/* int32 */
				0xce, 0x00, 0x01, 0x00, 0x00,
				0xce, 0xff, 0xff, 0xff, 0xff,

				/* int64 */
				0xcf, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
				0xcf, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
			};

			Test (delegate (MsgPackWriter writer) {
				for (int i = 0; i < nums.Length; i ++) {
					writer.Write (nums[i]);
				}
			}, delegate (MsgPackReader reader) {
				for (int i = 0; i < nums.Length; i ++) {
					Assert.IsTrue (reader.Read ());
					Assert.IsTrue (reader.IsUnsigned () || reader.IsUnsigned64 ());
					if (reader.IsUnsigned64 ()) {
						Assert.AreEqual (nums[i], reader.ValueUnsigned64);
					} else {
						Assert.AreEqual (nums[i], reader.ValueUnsigned);
					}
				}
			}, expectedBytes);
		}

		[Test]
		public void NilTest ()
		{
			byte[] expectedBytes = new byte[] {
				0xc0
			};

			Test (delegate (MsgPackWriter writer) {
				writer.WriteNil ();
			}, delegate (MsgPackReader reader) {
				Assert.IsTrue (reader.Read ());
				Assert.IsTrue (reader.Type == TypePrefixes.Nil);
			}, expectedBytes);
		}

		[Test]
		public void BooleanTest ()
		{
			byte[] expectedBytes = new byte[] {
				0xc3, 0xc2
			};

			Test (delegate (MsgPackWriter writer) {
				writer.Write (true);
				writer.Write (false);
			}, delegate (MsgPackReader reader) {
				Assert.IsTrue (reader.Read ());
				Assert.IsTrue (reader.Type == TypePrefixes.True);
				Assert.IsTrue (reader.Read ());
				Assert.IsTrue (reader.Type == TypePrefixes.False);
			}, expectedBytes);
		}

		[Test]
		public void FloatingPointTest ()
		{
			byte[] expectedBytes = new byte[] {
				0xca, 0x40, 0x49, 0x0f, 0xdb,
				0xcb, 0x40, 0x09, 0x21, 0xfb, 0x54, 0x44, 0x2d, 0x18,
			};

			Test (delegate (MsgPackWriter writer) {
				writer.Write ((float)Math.PI);
				writer.Write (Math.PI);
			}, delegate (MsgPackReader reader) {
				Assert.IsTrue (reader.Read ());
				Assert.IsTrue (reader.Type == TypePrefixes.Float);
				Assert.AreEqual ((float)Math.PI, reader.ValueFloat);
				Assert.IsTrue (reader.Read ());
				Assert.IsTrue (reader.Type == TypePrefixes.Double);
				Assert.AreEqual (Math.PI, reader.ValueDouble);
			}, expectedBytes);
		}

		[Test]
		public void RawTest ()
		{
			Random rnd = new Random ();

			byte[][] rawList = new byte[][] {
				new byte[0],
				new byte[1],
				new byte[31],
				new byte[32],
				new byte[65535],
				new byte[65536]
			};
			byte[][] headerSizeList = new byte[][] {
				new byte[] {0xa0},
				new byte[] {0xa1},
				new byte[] {0xbf},
				new byte[] {0xda, 0x00, 0x20},
				new byte[] {0xda, 0xff, 0xff},
				new byte[] {0xdb, 0x00, 0x01, 0x00, 0x00},
			};
			byte[] expectedBytes = new byte[131135 + 1 * 3 + 3 * 2 + 5];
			for (int i = 0, offset = 0; i < rawList.Length; i ++) {
				rnd.NextBytes (rawList[i]);

				Buffer.BlockCopy (headerSizeList[i], 0, expectedBytes, offset, headerSizeList[i].Length);
				offset += headerSizeList[i].Length;
				Buffer.BlockCopy (rawList[i], 0, expectedBytes, offset, rawList[i].Length);
				offset += rawList[i].Length;
			}

			Test (delegate (MsgPackWriter writer) {
				for (int i = 0; i < rawList.Length; i ++)
					writer.Write (rawList[i]);
			}, delegate (MsgPackReader reader) {
				for (int i = 0; i < rawList.Length; i ++) {
					Assert.IsTrue (reader.Read ());
					Assert.AreEqual (rawList[i].Length, (int)reader.Length);
					byte[] tmp = new byte[(int)reader.Length];
					reader.ReadValueRaw (tmp, 0, tmp.Length);
					Assert.AreEqual (rawList[i], tmp);
				}
			}, expectedBytes);
		}

		[Test]
		public void ArrayMapRawHeaderTest ()
		{
			int[] list = new int[] {
				0, 1, 15, 16, 31, 32, 65535, 65536
			};
			byte[] expectedBytes = new byte[] {
				/* size=0 */
				0x90, /* array */
				0x80, /* map */
				0xa0, /* raw */
				
				/* size=1 */
				0x91,
				0x81,
				0xa1,
				
				/* size=15 */
				0x9f,
				0x8f,
				0xaf,

				/* size=16 */
				0xdc, 0x00, 0x10, /* array16 */
				0xde, 0x00, 0x10, /* map16 */
				0xb0, /* fix raw */

				/* size=31 */
				0xdc, 0x00, 0x1f, /* array16 */
				0xde, 0x00, 0x1f, /* map16 */
				0xbf, /* fix raw */

				/* size=32 */
				0xdc, 0x00, 0x20, /* array16 */
				0xde, 0x00, 0x20, /* map16 */
				0xda, 0x00, 0x20, /* raw16 */

				/* size=65535 */
				0xdc, 0xff, 0xff, /* array16 */
				0xde, 0xff, 0xff, /* map16 */
				0xda, 0xff, 0xff, /* raw16 */

				/* size=65536 */
				0xdd, 0x00, 0x01, 0x00, 0x00, /* array32 */
				0xdf, 0x00, 0x01, 0x00, 0x00, /* map32 */
				0xdb, 0x00, 0x01, 0x00, 0x00, /* raw32 */
			};

			Test (delegate (MsgPackWriter writer) {
				for (int i = 0; i < list.Length; i ++) {
					writer.WriteArrayHeader (list[i]);
					writer.WriteMapHeader (list[i]);
					writer.WriteRawHeader (list[i]);
				}
			}, delegate (MsgPackReader reader) {
				for (int i = 0; i < list.Length; i ++) {
					Assert.IsTrue (reader.Read ());
					Assert.IsTrue (reader.IsArray ());
					Assert.AreEqual (list[i], (int)reader.Length);
					Assert.IsTrue (reader.Read ());
					Assert.IsTrue (reader.IsMap ());
					Assert.AreEqual (list[i], (int)reader.Length);
					Assert.IsTrue (reader.Read ());
					Assert.IsTrue (reader.IsRaw ());
					Assert.AreEqual (list[i], (int)reader.Length);
				}
			}, expectedBytes);
		}

		delegate void WriteDelegate (MsgPackWriter writer);
		delegate void ReadDelegate (MsgPackReader reader);
		void Test (WriteDelegate writeProc, ReadDelegate readProc, byte[] expectedBytes)
		{
			byte[] raw;
			using (MemoryStream ms = new MemoryStream ()) {
				MsgPackWriter writer = new MsgPackWriter (ms);
				writeProc (writer);
				raw = ms.ToArray ();
			}
			Assert.AreEqual (expectedBytes, raw, "pack failed");
			using (MemoryStream ms = new MemoryStream (raw)) {
				MsgPackReader reader = new MsgPackReader (ms);
				readProc (reader);
			}
		}
	}
}
