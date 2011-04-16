using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using msgpack.Compiler;

namespace msgpack
{
	public class CompiledPacker
	{
		public static byte[] Pack (object o)
		{
			using (MemoryStream ms = new MemoryStream ()) {
				Pack (ms, o);
				return ms.ToArray ();
			}
		}

		public static void Pack (Stream strm, object o)
		{
			PackerCompiler.GetPackMethod (o.GetType ()) (new MsgPackWriter (strm), o);
		}

		public static byte[] Pack<T> (T o)
		{
			using (MemoryStream ms = new MemoryStream ()) {
				Pack<T> (ms, o);
				return ms.ToArray ();
			}
		}

		public static void Pack<T> (Stream strm, T o)
		{
			PackerCompiler.GetPackMethod<T> () (new MsgPackWriter (strm), o);
		}

		public static T Unpack<T> (byte[] buf)
		{
			return Unpack<T> (buf, 0, buf.Length);
		}

		public static T Unpack<T> (byte[] buf, int offset, int size)
		{
			using (MemoryStream ms = new MemoryStream (buf, offset, size)) {
				return Unpack<T> (ms);
			}
		}

		public static T Unpack<T> (Stream strm)
		{
			return PackerCompiler.GetUnpackMethod<T> () (new MsgPackReader (strm));
		}

		public static object Unpack (Type t, byte[] buf)
		{
			return Unpack (t, buf, 0, buf.Length);
		}

		public static object Unpack (Type t, byte[] buf, int offset, int size)
		{
			using (MemoryStream ms = new MemoryStream (buf, offset, size)) {
				return Unpack (t, ms);
			}
		}

		public static object Unpack (Type t, Stream strm)
		{
			throw new NotImplementedException ();
		}
	}
}
