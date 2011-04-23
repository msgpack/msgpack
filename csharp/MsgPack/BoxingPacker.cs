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
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Reflection;

namespace MsgPack
{
	public class BoxingPacker
	{
		static Type KeyValuePairDefinitionType;

		static BoxingPacker ()
		{
			KeyValuePairDefinitionType = typeof (KeyValuePair<object,object>).GetGenericTypeDefinition ();
		}

		public void Pack (Stream strm, object o)
		{
			MsgPackWriter writer = new MsgPackWriter (strm);
			Pack (writer, o);
		}

		public byte[] Pack (object o)
		{
			using (MemoryStream ms = new MemoryStream ()) {
				Pack (ms, o);
				return ms.ToArray ();
			}
		}

		void Pack (MsgPackWriter writer, object o)
		{
			if (o == null) {
				writer.WriteNil ();
				return;
			}

			Type t = o.GetType ();
			if (t.IsPrimitive) {
				if (t.Equals (typeof (int))) writer.Write ((int)o);
				else if (t.Equals (typeof (uint))) writer.Write ((uint)o);
				else if (t.Equals (typeof (float))) writer.Write ((float)o);
				else if (t.Equals (typeof (double))) writer.Write ((double)o);
				else if (t.Equals (typeof (long))) writer.Write ((long)o);
				else if (t.Equals (typeof (ulong))) writer.Write ((ulong)o);
				else if (t.Equals (typeof (bool))) writer.Write ((bool)o);
				else if (t.Equals (typeof (byte))) writer.Write ((byte)o);
				else if (t.Equals (typeof (sbyte))) writer.Write ((sbyte)o);
				else if (t.Equals (typeof (short))) writer.Write ((short)o);
				else if (t.Equals (typeof (ushort))) writer.Write ((ushort)o);
				else throw new NotSupportedException ();  // char?
				return;
			}

			IDictionary dic = o as IDictionary;
			if (dic != null) {
				writer.WriteMapHeader (dic.Count);
				foreach (System.Collections.DictionaryEntry e in dic) {
					Pack (writer, e.Key);
					Pack (writer, e.Value);
				}
				return;
			}
			
			if (t.IsArray) {
				Array ary = (Array)o;
				Type et = t.GetElementType ();

				// KeyValuePair<K,V>[] (Map Type)
				if (et.IsGenericType && et.GetGenericTypeDefinition ().Equals (KeyValuePairDefinitionType)) {
					PropertyInfo propKey = et.GetProperty ("Key");
					PropertyInfo propValue = et.GetProperty ("Value");
					writer.WriteMapHeader (ary.Length);
					for (int i = 0; i < ary.Length; i ++) {
						object e = ary.GetValue (i);
						Pack (writer, propKey.GetValue (e, null));
						Pack (writer, propValue.GetValue (e, null));
					}
					return;
				}

				// Array
				writer.WriteArrayHeader (ary.Length);
				for (int i = 0; i < ary.Length; i ++)
					Pack (writer, ary.GetValue (i));
				return;
			}
		}

		public object Unpack (Stream strm)
		{
			MsgPackReader reader = new MsgPackReader (strm);
			return Unpack (reader);
		}

		public object Unpack (byte[] buf, int offset, int size)
		{
			using (MemoryStream ms = new MemoryStream (buf, offset, size)) {
				return Unpack (ms);
			}
		}

		public object Unpack (byte[] buf)
		{
			return Unpack (buf, 0, buf.Length);
		}

		object Unpack (MsgPackReader reader)
		{
			if (!reader.Read ())
				throw new FormatException ();

			switch (reader.Type) {
				case TypePrefixes.PositiveFixNum:
				case TypePrefixes.NegativeFixNum:
				case TypePrefixes.Int8:
				case TypePrefixes.Int16:
				case TypePrefixes.Int32:
					return reader.ValueSigned;
				case TypePrefixes.Int64:
					return reader.ValueSigned64;
				case TypePrefixes.UInt8:
				case TypePrefixes.UInt16:
				case TypePrefixes.UInt32:
					return reader.ValueUnsigned;
				case TypePrefixes.UInt64:
					return reader.ValueUnsigned64;
				case TypePrefixes.True:
					return true;
				case TypePrefixes.False:
					return false;
				case TypePrefixes.Float:
					return reader.ValueFloat;
				case TypePrefixes.Double:
					return reader.ValueDouble;
				case TypePrefixes.Nil:
					return null;
				case TypePrefixes.FixRaw:
				case TypePrefixes.Raw16:
				case TypePrefixes.Raw32:
					byte[] raw = new byte[reader.Length];
					reader.ReadValueRaw (raw, 0, raw.Length);
					return raw;
				case TypePrefixes.FixArray:
				case TypePrefixes.Array16:
				case TypePrefixes.Array32:
					object[] ary = new object[reader.Length];
					for (int i = 0; i < ary.Length; i ++)
						ary[i] = Unpack (reader);
					return ary;
				case TypePrefixes.FixMap:
				case TypePrefixes.Map16:
				case TypePrefixes.Map32:
					IDictionary<object, object> dic = new Dictionary<object, object> ((int)reader.Length);
					int count = (int)reader.Length;
					for (int i = 0; i < count; i ++) {
						object k = Unpack (reader);
						object v = Unpack (reader);
						dic.Add (k, v);
					}
					return dic;
				default:
					throw new FormatException ();
			}
		}
	}
}
