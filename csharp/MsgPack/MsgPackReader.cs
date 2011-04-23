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
using System.Text;

namespace MsgPack
{
	public class MsgPackReader
	{
		Stream _strm;
		byte[] _tmp0 = new byte[8];
		byte[] _tmp1 = new byte[8];

		Encoding _encoding = Encoding.UTF8;
		Decoder _decoder = Encoding.UTF8.GetDecoder ();
		byte[] _buf = new byte[64];

		public MsgPackReader (Stream strm)
		{
			_strm = strm;
		}

		public TypePrefixes Type { get; private set; }

		public bool ValueBoolean { get; private set; }
		public uint Length { get; private set; }

		public uint ValueUnsigned { get; private set; }
		public ulong ValueUnsigned64 { get; private set; }

		public int ValueSigned { get; private set; }
		public long ValueSigned64 { get; private set; }

		public float ValueFloat { get; private set; }
		public double ValueDouble { get; private set; }

		public bool IsSigned ()
		{
			return this.Type == TypePrefixes.NegativeFixNum ||
				this.Type == TypePrefixes.PositiveFixNum ||
				this.Type == TypePrefixes.Int8 ||
				this.Type == TypePrefixes.Int16 ||
				this.Type == TypePrefixes.Int32;
		}

		public bool IsBoolean ()
		{
			return this.Type == TypePrefixes.True || this.Type == TypePrefixes.False;
		}

		public bool IsSigned64 ()
		{
			return this.Type == TypePrefixes.Int64;
		}

		public bool IsUnsigned ()
		{
			return this.Type == TypePrefixes.PositiveFixNum ||
				this.Type == TypePrefixes.UInt8 ||
				this.Type == TypePrefixes.UInt16 ||
				this.Type == TypePrefixes.UInt32;
		}

		public bool IsUnsigned64 ()
		{
			return this.Type == TypePrefixes.UInt64;
		}

		public bool IsRaw ()
		{
			return this.Type == TypePrefixes.FixRaw || this.Type == TypePrefixes.Raw16 || this.Type == TypePrefixes.Raw32;
		}

		public bool IsArray ()
		{
			return this.Type == TypePrefixes.FixArray || this.Type == TypePrefixes.Array16 || this.Type == TypePrefixes.Array32;
		}

		public bool IsMap ()
		{
			return this.Type == TypePrefixes.FixMap || this.Type == TypePrefixes.Map16 || this.Type == TypePrefixes.Map32;
		}

		public bool Read ()
		{
			byte[] tmp0 = _tmp0, tmp1 = _tmp1;
			int x = _strm.ReadByte ();
			if (x < 0)
				return false; // EOS
			
			if (x >= 0x00 && x <= 0x7f) {
				this.Type = TypePrefixes.PositiveFixNum;
			} else if (x >= 0xe0 && x <= 0xff) {
				this.Type = TypePrefixes.NegativeFixNum;
			} else if (x >= 0xa0 && x <= 0xbf) {
				this.Type = TypePrefixes.FixRaw;
			} else if (x >= 0x90 && x <= 0x9f) {
				this.Type = TypePrefixes.FixArray;
			} else if (x >= 0x80 && x <= 0x8f) {
				this.Type = TypePrefixes.FixMap;
			} else {
				this.Type = (TypePrefixes)x;
			}

			switch (this.Type) {
				case TypePrefixes.Nil:
					break;
				case TypePrefixes.False:
					ValueBoolean = false;
					break;
				case TypePrefixes.True:
					ValueBoolean = true;
					break;
				case TypePrefixes.Float:
					_strm.Read (tmp0, 0, 4);
					if (BitConverter.IsLittleEndian) {
						tmp1[0] = tmp0[3];
						tmp1[1] = tmp0[2];
						tmp1[2] = tmp0[1];
						tmp1[3] = tmp0[0];
						ValueFloat = BitConverter.ToSingle (tmp1, 0);
					} else {
						ValueFloat = BitConverter.ToSingle (tmp0, 0);
					}
					break;
				case TypePrefixes.Double:
					_strm.Read (tmp0, 0, 8);
					if (BitConverter.IsLittleEndian) {
						tmp1[0] = tmp0[7];
						tmp1[1] = tmp0[6];
						tmp1[2] = tmp0[5];
						tmp1[3] = tmp0[4];
						tmp1[4] = tmp0[3];
						tmp1[5] = tmp0[2];
						tmp1[6] = tmp0[1];
						tmp1[7] = tmp0[0];
						ValueDouble = BitConverter.ToDouble (tmp1, 0);
					} else {
						ValueDouble = BitConverter.ToDouble (tmp0, 0);
					}
					break;
				case TypePrefixes.NegativeFixNum:
					ValueSigned = (x & 0x1f) - 0x20;
					break;
				case TypePrefixes.PositiveFixNum:
					ValueSigned = x & 0x7f;
					ValueUnsigned = (uint)ValueSigned;
					break;
				case TypePrefixes.UInt8:
					x = _strm.ReadByte ();
					if (x < 0)
						throw new FormatException ();
					ValueUnsigned = (uint)x;
					break;
				case TypePrefixes.UInt16:
					if (_strm.Read (tmp0, 0, 2) != 2)
						throw new FormatException ();
					ValueUnsigned = ((uint)tmp0[0] << 8) | (uint)tmp0[1];
					break;
				case TypePrefixes.UInt32:
					if (_strm.Read (tmp0, 0, 4) != 4)
						throw new FormatException ();
					ValueUnsigned = ((uint)tmp0[0] << 24) | ((uint)tmp0[1] << 16) | ((uint)tmp0[2] << 8) | (uint)tmp0[3];
					break;
				case TypePrefixes.UInt64:
					if (_strm.Read (tmp0, 0, 8) != 8)
						throw new FormatException ();
					ValueUnsigned64 = ((ulong)tmp0[0] << 56) | ((ulong)tmp0[1] << 48) | ((ulong)tmp0[2] << 40) | ((ulong)tmp0[3] << 32) | ((ulong)tmp0[4] << 24) | ((ulong)tmp0[5] << 16) | ((ulong)tmp0[6] << 8) | (ulong)tmp0[7];
					break;
				case TypePrefixes.Int8:
					x = _strm.ReadByte ();
					if (x < 0)
						throw new FormatException ();
					ValueSigned = (sbyte)x;
					break;
				case TypePrefixes.Int16:
					if (_strm.Read (tmp0, 0, 2) != 2)
						throw new FormatException ();
					ValueSigned = (short)((tmp0[0] << 8) | tmp0[1]);
					break;
				case TypePrefixes.Int32:
					if (_strm.Read (tmp0, 0, 4) != 4)
						throw new FormatException ();
					ValueSigned = (tmp0[0] << 24) | (tmp0[1] << 16) | (tmp0[2] << 8) | tmp0[3];
					break;
				case TypePrefixes.Int64:
					if (_strm.Read (tmp0, 0, 8) != 8)
						throw new FormatException ();
					ValueSigned64 = ((long)tmp0[0] << 56) | ((long)tmp0[1] << 48) | ((long)tmp0[2] << 40) | ((long)tmp0[3] << 32) | ((long)tmp0[4] << 24) | ((long)tmp0[5] << 16) | ((long)tmp0[6] << 8) | (long)tmp0[7];
					break;
				case TypePrefixes.FixRaw:
					Length = (uint)(x & 0x1f);
					break;
				case TypePrefixes.FixArray:
				case TypePrefixes.FixMap:
					Length = (uint)(x & 0xf);
					break;
				case TypePrefixes.Raw16:
				case TypePrefixes.Array16:
				case TypePrefixes.Map16:
					if (_strm.Read (tmp0, 0, 2) != 2)
						throw new FormatException ();
					Length = ((uint)tmp0[0] << 8) | (uint)tmp0[1];
					break;
				case TypePrefixes.Raw32:
				case TypePrefixes.Array32:
				case TypePrefixes.Map32:
					if (_strm.Read (tmp0, 0, 4) != 4)
						throw new FormatException ();
					Length = ((uint)tmp0[0] << 24) | ((uint)tmp0[1] << 16) | ((uint)tmp0[2] << 8) | (uint)tmp0[3];
					break;
				default:
					throw new FormatException ();
			}
			return true;
		}

		public int ReadValueRaw (byte[] buf, int offset, int count)
		{
			return _strm.Read (buf, offset, count);
		}

		public string ReadRawString ()
		{
			return ReadRawString (_buf);
		}

		public unsafe string ReadRawString (byte[] buf)
		{
			if (this.Length < buf.Length) {
				if (ReadValueRaw (buf, 0, (int)this.Length) != this.Length)
					throw new FormatException ();
				return _encoding.GetString (buf, 0, (int)this.Length);
			}

			// Poor implementation
			byte[] tmp = new byte[(int)this.Length];
			if (ReadValueRaw (tmp, 0, tmp.Length) != tmp.Length)
				throw new FormatException ();
			return _encoding.GetString (tmp);
		}
	}
}
