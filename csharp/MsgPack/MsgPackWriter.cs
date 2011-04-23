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
	public class MsgPackWriter
	{
		Stream _strm;
		Encoding _encoding = Encoding.UTF8;
		Encoder _encoder = Encoding.UTF8.GetEncoder ();
		byte[] _tmp = new byte[9];
		byte[] _buf = new byte[64];

		public MsgPackWriter (Stream strm)
		{
			_strm = strm;
		}

		public void Write (byte x)
		{
			if (x < 128) {
				_strm.WriteByte (x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xcc; 
				tmp[1] = x;
				_strm.Write (tmp, 0, 2);
			}
		}

		public void Write (ushort x)
		{
			if (x < 0x100) {
				Write ((byte)x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xcd; 
				tmp[1] = (byte)(x >> 8);
				tmp[2] = (byte)x;
				_strm.Write (tmp, 0, 3);
			}
		}

		public void Write (char x)
		{
			Write ((ushort)x);
		}

		public void Write (uint x)
		{
			if (x < 0x10000) {
				Write ((ushort)x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xce; 
				tmp[1] = (byte)(x >> 24);
				tmp[2] = (byte)(x >> 16);
				tmp[3] = (byte)(x >>  8);
				tmp[4] = (byte)x;
				_strm.Write (tmp, 0, 5);
			}
		}

		public void Write (ulong x)
		{
			if (x < 0x100000000) {
				Write ((uint)x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xcf; 
				tmp[1] = (byte)(x >> 56);
				tmp[2] = (byte)(x >> 48);
				tmp[3] = (byte)(x >> 40);
				tmp[4] = (byte)(x >> 32);
				tmp[5] = (byte)(x >> 24);
				tmp[6] = (byte)(x >> 16);
				tmp[7] = (byte)(x >>  8);
				tmp[8] = (byte)x;
				_strm.Write (tmp, 0, 9);
			}
		}

		public void Write (sbyte x)
		{
			if (x >= -32 && x <= -1) {
				_strm.WriteByte ((byte)(0xe0 | (byte)x));
			} else if (x >= 0 && x <= 127) {
				_strm.WriteByte ((byte)x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xd0;
				tmp[1] = (byte)x;
				_strm.Write (tmp, 0, 2);
			}
		}

		public void Write (short x)
		{
			if (x >= sbyte.MinValue && x <= sbyte.MaxValue) {
				Write ((sbyte)x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xd1;
				tmp[1] = (byte)(x >> 8);
				tmp[2] = (byte)x;
				_strm.Write (tmp, 0, 3);
			}
		}

		public void Write (int x)
		{
			if (x >= short.MinValue && x <= short.MaxValue) {
				Write ((short)x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xd2;
				tmp[1] = (byte)(x >> 24);
				tmp[2] = (byte)(x >> 16);
				tmp[3] = (byte)(x >> 8);
				tmp[4] = (byte)x;
				_strm.Write (tmp, 0, 5);
			}
		}

		public void Write (long x)
		{
			if (x >= int.MinValue && x <= int.MaxValue) {
				Write ((int)x);
			} else {
				byte[] tmp = _tmp;
				tmp[0] = 0xd3;
				tmp[1] = (byte)(x >> 56);
				tmp[2] = (byte)(x >> 48);
				tmp[3] = (byte)(x >> 40);
				tmp[4] = (byte)(x >> 32);
				tmp[5] = (byte)(x >> 24);
				tmp[6] = (byte)(x >> 16);
				tmp[7] = (byte)(x >> 8);
				tmp[8] = (byte)x;
				_strm.Write (tmp, 0, 9);
			}
		}

		public void WriteNil ()
		{
			_strm.WriteByte (0xc0);
		}

		public void Write (bool x)
		{
			_strm.WriteByte ((byte)(x ? 0xc3 : 0xc2));
		}

		public void Write (float x)
		{
			byte[] raw = BitConverter.GetBytes (x); // unsafeコードを使う?
			byte[] tmp = _tmp;

			tmp[0] = 0xca;
			if (BitConverter.IsLittleEndian) {
				tmp[1] = raw[3];
				tmp[2] = raw[2];
				tmp[3] = raw[1];
				tmp[4] = raw[0];
			} else {
				tmp[1] = raw[0];
				tmp[2] = raw[1];
				tmp[3] = raw[2];
				tmp[4] = raw[3];
			}
			_strm.Write (tmp, 0, 5);
		}

		public void Write (double x)
		{
			byte[] raw = BitConverter.GetBytes (x); // unsafeコードを使う?
			byte[] tmp = _tmp;

			tmp[0] = 0xcb;
			if (BitConverter.IsLittleEndian) {
				tmp[1] = raw[7];
				tmp[2] = raw[6];
				tmp[3] = raw[5];
				tmp[4] = raw[4];
				tmp[5] = raw[3];
				tmp[6] = raw[2];
				tmp[7] = raw[1];
				tmp[8] = raw[0];
			} else {
				tmp[1] = raw[0];
				tmp[2] = raw[1];
				tmp[3] = raw[2];
				tmp[4] = raw[3];
				tmp[5] = raw[4];
				tmp[6] = raw[5];
				tmp[7] = raw[6];
				tmp[8] = raw[7];
			}
			_strm.Write (tmp, 0, 9);
		}
		
		public void Write (byte[] bytes)
		{
			WriteRawHeader (bytes.Length);
			_strm.Write (bytes, 0, bytes.Length);
		}

		public void WriteRawHeader (int N)
		{
			WriteLengthHeader (N, 32, 0xa0, 0xda, 0xdb);
		}

		public void WriteArrayHeader (int N)
		{
			WriteLengthHeader (N, 16, 0x90, 0xdc, 0xdd);
		}

		public void WriteMapHeader (int N)
		{
			WriteLengthHeader (N, 16, 0x80, 0xde, 0xdf);
		}

		void WriteLengthHeader (int N, int fix_length, byte fix_prefix, byte len16bit_prefix, byte len32bit_prefix)
		{
			if (N < fix_length) {
				_strm.WriteByte ((byte)(fix_prefix | N));
			} else {
				byte[] tmp = _tmp;
				int header_len;
				if (N < 0x10000) {
					tmp[0] = len16bit_prefix;
					tmp[1] = (byte)(N >> 8);
					tmp[2] = (byte)N;
					header_len = 3;
				} else {
					tmp[0] = len32bit_prefix;
					tmp[1] = (byte)(N >> 24);
					tmp[2] = (byte)(N >> 16);
					tmp[3] = (byte)(N >>  8);
					tmp[4] = (byte)N;
					header_len = 5;
				}
				_strm.Write (tmp, 0, header_len);
			}
		}

		public void Write (string x)
		{
			Write (x, false);
		}
		
		public void Write (string x, bool highProbAscii)
		{
			Write (x, _buf, highProbAscii);
		}

		public void Write (string x, byte[] buf)
		{
			Write (x, buf, false);
		}

		public unsafe void Write (string x, byte[] buf, bool highProbAscii)
		{
			Encoder encoder = _encoder;
			fixed (char *pstr = x)
			fixed (byte *pbuf = buf) {
				if (highProbAscii && x.Length <= buf.Length) {
					bool isAsciiFullCompatible = true;
					for (int i = 0; i < x.Length; i ++) {
						int v = (int)pstr[i];
						if (v > 0x7f) {
							isAsciiFullCompatible = false;
							break;
						}
						buf[i] = (byte)v;
					}
					if (isAsciiFullCompatible) {
						WriteRawHeader (x.Length);
						_strm.Write (buf, 0, x.Length);
						return;
					}
				}

				WriteRawHeader (encoder.GetByteCount (pstr, x.Length, true));
				int str_len = x.Length;
				char *p = pstr;
				int convertedChars, bytesUsed;
				bool completed = true;
				while (str_len > 0 || !completed) {
					encoder.Convert (p, str_len, pbuf, buf.Length, false, out convertedChars, out bytesUsed, out completed);
					_strm.Write (buf, 0, bytesUsed);
					str_len -= convertedChars;
					p += convertedChars;
				}
			}
		}
	}
}
