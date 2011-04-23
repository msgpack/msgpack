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
using System.IO;
using System.Reflection;
using System.Reflection.Emit;
using System.Threading;
using MsgPack.Compiler;

namespace MsgPack
{
	public class CompiledPacker
	{
		static PackerBase _publicFieldPacker, _allFieldPacker;
		PackerBase _packer;

		static CompiledPacker ()
		{
			_publicFieldPacker = new MethodBuilderPacker ();
			_allFieldPacker = new DynamicMethodPacker ();
		}

		public CompiledPacker () : this (false) {}
		public CompiledPacker (bool packPrivateField)
		{
			_packer = (packPrivateField ? _allFieldPacker : _publicFieldPacker);
		}

		public void Prepare<T> ()
		{
			_packer.CreatePacker<T> ();
			_packer.CreateUnpacker<T> ();
		}

		#region Generics Pack/Unpack Methods
		public byte[] Pack<T> (T o)
		{
			using (MemoryStream ms = new MemoryStream ()) {
				Pack<T> (ms, o);
				return ms.ToArray ();
			}
		}

		public void Pack<T> (Stream strm, T o)
		{
			_packer.CreatePacker<T> () (new MsgPackWriter (strm), o);
		}

		public T Unpack<T> (byte[] buf)
		{
			return Unpack<T> (buf, 0, buf.Length);
		}

		public T Unpack<T> (byte[] buf, int offset, int size)
		{
			using (MemoryStream ms = new MemoryStream (buf, offset, size)) {
				return Unpack<T> (ms);
			}
		}

		public T Unpack<T> (Stream strm)
		{
			return _packer.CreateUnpacker<T> () (new MsgPackReader (strm));
		}
		#endregion

		#region Non-generics Pack/Unpack Methods
		public byte[] Pack (object o)
		{
			using (MemoryStream ms = new MemoryStream ()) {
				Pack (ms, o);
				return ms.ToArray ();
			}
		}

		public void Pack (Stream strm, object o)
		{
			throw new NotImplementedException ();
		}

		public object Unpack (Type t, byte[] buf)
		{
			return Unpack (t, buf, 0, buf.Length);
		}

		public object Unpack (Type t, byte[] buf, int offset, int size)
		{
			using (MemoryStream ms = new MemoryStream (buf, offset, size)) {
				return Unpack (t, ms);
			}
		}

		public object Unpack (Type t, Stream strm)
		{
			throw new NotImplementedException ();
		}
		#endregion

		#region Compiled Packer Implementations
		public abstract class PackerBase
		{
			Dictionary<Type, Delegate> _packers = new Dictionary<Type, Delegate> ();
			Dictionary<Type, Delegate> _unpackers = new Dictionary<Type, Delegate> ();

			protected Dictionary<Type, MethodInfo> _packMethods = new Dictionary<Type, MethodInfo> ();
			protected Dictionary<Type, MethodInfo> _unpackMethods = new Dictionary<Type, MethodInfo> ();

			protected PackerBase ()
			{
				DefaultPackMethods.Register (_packMethods, _unpackMethods);
			}

			public Action<MsgPackWriter, T> CreatePacker<T> ()
			{
				Delegate d;
				lock (_packers) {
					if (!_packers.TryGetValue (typeof (T), out d)) {
						d = CreatePacker_Internal<T> ();
						_packers.Add (typeof (T), d);
					}
				}
				return (Action<MsgPackWriter, T>)d;
			}

			public Func<MsgPackReader, T> CreateUnpacker<T> ()
			{
				Delegate d;
				lock (_unpackers) {
					if (!_unpackers.TryGetValue (typeof (T), out d)) {
						d = CreateUnpacker_Internal<T> ();
						_unpackers.Add (typeof (T), d);
					}
				}
				return (Func<MsgPackReader, T>)d;
			}

			protected abstract Action<MsgPackWriter, T> CreatePacker_Internal<T> ();
			protected abstract Func<MsgPackReader, T> CreateUnpacker_Internal<T> ();
		}
		public sealed class DynamicMethodPacker : PackerBase
		{
			protected static MethodInfo LookupMemberMappingMethod;
			static Dictionary<Type, IDictionary<string, int>> UnpackMemberMappings;

			static DynamicMethodPacker ()
			{
				UnpackMemberMappings = new Dictionary<Type, IDictionary<string, int>> ();
				LookupMemberMappingMethod = typeof (DynamicMethodPacker).GetMethod ("LookupMemberMapping", BindingFlags.Static | BindingFlags.NonPublic);
			}

			public DynamicMethodPacker () : base ()
			{
			}

			protected override Action<MsgPackWriter, T> CreatePacker_Internal<T> ()
			{
				DynamicMethod dm = CreatePacker (typeof (T), CreatePackDynamicMethod (typeof (T)));
				return (Action<MsgPackWriter, T>)dm.CreateDelegate (typeof (Action<MsgPackWriter, T>));
			}

			protected override Func<MsgPackReader, T> CreateUnpacker_Internal<T> ()
			{
				DynamicMethod dm = CreateUnpacker (typeof (T), CreateUnpackDynamicMethod (typeof (T)));
				return (Func<MsgPackReader, T>)dm.CreateDelegate (typeof (Func<MsgPackReader, T>));
			}

			DynamicMethod CreatePacker (Type t, DynamicMethod dm)
			{
				ILGenerator il = dm.GetILGenerator ();
				_packMethods.Add (t, dm);
				PackILGenerator.EmitPackCode (t, dm, il, LookupMembers, FormatMemberName, LookupPackMethod);
				return dm;
			}

			DynamicMethod CreateUnpacker (Type t, DynamicMethod dm)
			{
				ILGenerator il = dm.GetILGenerator ();
				_unpackMethods.Add (t, dm);
				PackILGenerator.EmitUnpackCode (t, dm, il, LookupMembers, FormatMemberName, LookupUnpackMethod,
					LookupMemberMapping, LookupMemberMappingMethod);
				return dm;
			}

			static DynamicMethod CreatePackDynamicMethod (Type t)
			{
				return CreateDynamicMethod (typeof (void), new Type[] {typeof (MsgPackWriter), t});
			}

			static DynamicMethod CreateUnpackDynamicMethod (Type t)
			{
				return CreateDynamicMethod (t, new Type[] {typeof (MsgPackReader)});
			}

			static MemberInfo[] LookupMembers (Type t)
			{
				BindingFlags baseFlags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
				List<MemberInfo> list = new List<MemberInfo> ();
				list.AddRange (t.GetFields (baseFlags));
				// TODO: Add NonSerialized Attribute Filter ?
				return list.ToArray ();
			}

			MethodInfo LookupPackMethod (Type t)
			{
				MethodInfo mi;
				DynamicMethod dm;
				if (_packMethods.TryGetValue (t, out mi))
					return mi;
				dm = CreatePackDynamicMethod (t);
				return CreatePacker (t, dm);
			}

			MethodInfo LookupUnpackMethod (Type t)
			{
				MethodInfo mi;
				if (_unpackMethods.TryGetValue (t, out mi))
					return mi;
				DynamicMethod dm = CreateUnpackDynamicMethod (t);
				return CreateUnpacker (t, dm);
			}

			static string FormatMemberName (MemberInfo m)
			{
				if (m.MemberType != MemberTypes.Field)
					return m.Name;

				int pos;
				string name = m.Name;
				if (name[0] == '<' && (pos = name.IndexOf ('>')) > 1)
					name = name.Substring (1, pos - 1); // Auto-Property (\<.+\>) <ab>
				return name;
			}

			static int _dynamicMethodIdx = 0;
			static DynamicMethod CreateDynamicMethod (Type returnType, Type[] parameterTypes)
			{
				string name = "_" + Interlocked.Increment (ref _dynamicMethodIdx).ToString ();
				return new DynamicMethod (name, returnType, parameterTypes, true);
			}

			internal static IDictionary<string,int> LookupMemberMapping (Type t)
			{
				IDictionary<string, int> mapping;
				lock (UnpackMemberMappings) {
					if (!UnpackMemberMappings.TryGetValue (t, out mapping)) {
						mapping = new Dictionary<string, int> ();
						UnpackMemberMappings.Add (t, mapping);
					}
				}
				return mapping;
			}
		}
		public sealed class MethodBuilderPacker : PackerBase
		{
			public const string AssemblyName = "MessagePackInternalAssembly";
			static AssemblyName DynamicAsmName;
			static AssemblyBuilder DynamicAsmBuilder;
			static ModuleBuilder DynamicModuleBuilder;

			protected static MethodInfo LookupMemberMappingMethod;
			static Dictionary<Type, IDictionary<string, int>> UnpackMemberMappings;

			static MethodBuilderPacker ()
			{
				UnpackMemberMappings = new Dictionary<Type, IDictionary<string, int>> ();
				LookupMemberMappingMethod = typeof (MethodBuilderPacker).GetMethod ("LookupMemberMapping", BindingFlags.Static | BindingFlags.NonPublic);

				DynamicAsmName = new AssemblyName (AssemblyName);
				DynamicAsmBuilder = AppDomain.CurrentDomain.DefineDynamicAssembly (DynamicAsmName, AssemblyBuilderAccess.Run);
				DynamicModuleBuilder = DynamicAsmBuilder.DefineDynamicModule (DynamicAsmName.Name);
			}

			public MethodBuilderPacker () : base ()
			{
			}

			protected override Action<MsgPackWriter, T> CreatePacker_Internal<T> ()
			{
				TypeBuilder tb;
				MethodBuilder mb;
				CreatePackMethodBuilder (typeof (T), out tb, out mb);
				_packMethods.Add (typeof (T), mb);
				CreatePacker (typeof (T), mb);
				MethodInfo mi = ToCallableMethodInfo (typeof (T), tb, true);
				return (Action<MsgPackWriter, T>)Delegate.CreateDelegate (typeof (Action<MsgPackWriter, T>), mi);
			}

			protected override Func<MsgPackReader, T> CreateUnpacker_Internal<T> ()
			{
				TypeBuilder tb;
				MethodBuilder mb;
				CreateUnpackMethodBuilder (typeof (T), out tb, out mb);
				_unpackMethods.Add (typeof (T), mb);
				CreateUnpacker (typeof (T), mb);
				MethodInfo mi = ToCallableMethodInfo (typeof (T), tb, false);
				return (Func<MsgPackReader, T>)Delegate.CreateDelegate (typeof (Func<MsgPackReader, T>), mi);
			}

			void CreatePacker (Type t, MethodBuilder mb)
			{
				ILGenerator il = mb.GetILGenerator ();
				PackILGenerator.EmitPackCode (t, mb, il, LookupMembers, FormatMemberName, LookupPackMethod);
			}

			void CreateUnpacker (Type t, MethodBuilder mb)
			{
				ILGenerator il = mb.GetILGenerator ();
				PackILGenerator.EmitUnpackCode (t, mb, il, LookupMembers, FormatMemberName, LookupUnpackMethod,
					LookupMemberMapping, LookupMemberMappingMethod);
			}

			MethodInfo ToCallableMethodInfo (Type t, TypeBuilder tb, bool isPacker)
			{
				Type type = tb.CreateType ();
				MethodInfo mi = type.GetMethod (isPacker ? "Pack" : "Unpack", BindingFlags.Static | BindingFlags.Public);
				if (isPacker) {
					_packMethods[t] = mi;
				} else {
					_unpackMethods[t] = mi;
				}
				return mi;
			}

			MethodInfo LookupPackMethod (Type t)
			{
				MethodInfo mi;
				TypeBuilder tb;
				MethodBuilder mb;
				if (_packMethods.TryGetValue (t, out mi))
					return mi;
				CreatePackMethodBuilder (t, out tb, out mb);
				_packMethods.Add (t, mb);
				CreatePacker (t, mb);
				return ToCallableMethodInfo (t, tb, true);
			}

			MethodInfo LookupUnpackMethod (Type t)
			{
				MethodInfo mi;
				TypeBuilder tb;
				MethodBuilder mb;
				if (_unpackMethods.TryGetValue (t, out mi))
					return mi;
				CreateUnpackMethodBuilder (t, out tb, out mb);
				_unpackMethods.Add (t, mb);
				CreateUnpacker (t, mb);
				return ToCallableMethodInfo (t, tb, false);
			}

			static string FormatMemberName (MemberInfo m)
			{
				return m.Name;
			}

			static MemberInfo[] LookupMembers (Type t)
			{
				BindingFlags baseFlags = BindingFlags.Instance | BindingFlags.Public;
				List<MemberInfo> list = new List<MemberInfo> ();
				list.AddRange (t.GetFields (baseFlags));
				// TODO: Add NonSerialized Attribute Filter ?
				return list.ToArray ();
			}

			static void CreatePackMethodBuilder (Type t, out TypeBuilder tb, out MethodBuilder mb)
			{
				tb = DynamicModuleBuilder.DefineType (t.Name + "PackerType", TypeAttributes.Public);
				mb = tb.DefineMethod ("Pack", MethodAttributes.Static | MethodAttributes.Public, typeof (void), new Type[] {typeof (MsgPackWriter), t});
			}

			static void CreateUnpackMethodBuilder (Type t, out TypeBuilder tb, out MethodBuilder mb)
			{
				tb = DynamicModuleBuilder.DefineType (t.Name + "UnpackerType", TypeAttributes.Public);
				mb = tb.DefineMethod ("Unpack", MethodAttributes.Static | MethodAttributes.Public, t, new Type[] {typeof (MsgPackReader)});
			}

			internal static IDictionary<string,int> LookupMemberMapping (Type t)
			{
				IDictionary<string, int> mapping;
				lock (UnpackMemberMappings) {
					if (!UnpackMemberMappings.TryGetValue (t, out mapping)) {
						mapping = new Dictionary<string, int> ();
						UnpackMemberMappings.Add (t, mapping);
					}
				}
				return mapping;
			}
		}
		#endregion

		#region default pack/unpack methods
		internal static class DefaultPackMethods
		{
			public static void Register (Dictionary<Type, MethodInfo> packMethods, Dictionary<Type, MethodInfo> unpackMethods)
			{
				RegisterPackMethods (packMethods);
				RegisterUnpackMethods (unpackMethods);
			}

			#region Pack
			static void RegisterPackMethods (Dictionary<Type, MethodInfo> packMethods)
			{
				Type type = typeof (DefaultPackMethods);
				MethodInfo[] methods = type.GetMethods (BindingFlags.Static | BindingFlags.NonPublic);
				string methodName = "Pack";
				for (int i = 0; i < methods.Length; i ++) {
					if (!methodName.Equals (methods[i].Name))
						continue;
					ParameterInfo[] parameters = methods[i].GetParameters ();
					if (parameters.Length != 2 || parameters[0].ParameterType != typeof (MsgPackWriter))
						continue;
					packMethods.Add (parameters[1].ParameterType, methods[i]);
				}
			}

			internal static void Pack (MsgPackWriter writer, string x)
			{
				if (x == null) {
					writer.WriteNil ();
				} else {
					writer.Write (x, false);
				}
			}
			#endregion

			#region Unpack
			static void RegisterUnpackMethods (Dictionary<Type, MethodInfo> unpackMethods)
			{
				BindingFlags flags = BindingFlags.Static | BindingFlags.NonPublic;
				Type type = typeof (DefaultPackMethods);
				MethodInfo mi = type.GetMethod ("Unpack_Signed", flags);
				unpackMethods.Add (typeof (sbyte), mi);
				unpackMethods.Add (typeof (short), mi);
				unpackMethods.Add (typeof (int), mi);

				mi = type.GetMethod ("Unpack_Signed64", flags);
				unpackMethods.Add (typeof (long), mi);

				mi = type.GetMethod ("Unpack_Unsigned", flags);
				unpackMethods.Add (typeof (byte), mi);
				unpackMethods.Add (typeof (ushort), mi);
				unpackMethods.Add (typeof (char), mi);
				unpackMethods.Add (typeof (uint), mi);

				mi = type.GetMethod ("Unpack_Unsigned64", flags);
				unpackMethods.Add (typeof (ulong), mi);

				mi = type.GetMethod ("Unpack_Boolean", flags);
				unpackMethods.Add (typeof (bool), mi);

				mi = type.GetMethod ("Unpack_Float", flags);
				unpackMethods.Add (typeof (float), mi);

				mi = type.GetMethod ("Unpack_Double", flags);
				unpackMethods.Add (typeof (double), mi);

				mi = type.GetMethod ("Unpack_String", flags);
				unpackMethods.Add (typeof (string), mi);
			}

			internal static int Unpack_Signed (MsgPackReader reader)
			{
				if (!reader.Read () || !reader.IsSigned ())
					UnpackFailed ();
				return reader.ValueSigned;
			}

			internal static long Unpack_Signed64 (MsgPackReader reader)
			{
				if (!reader.Read ())
					UnpackFailed ();
				if (reader.IsSigned ())
					return reader.ValueSigned;
				if (reader.IsSigned64 ())
					return reader.ValueSigned64;
				UnpackFailed ();
				return 0; // unused
			}

			internal static uint Unpack_Unsigned (MsgPackReader reader)
			{
				if (!reader.Read () || !reader.IsUnsigned ())
					UnpackFailed ();
				return reader.ValueUnsigned;
			}

			internal static ulong Unpack_Unsigned64 (MsgPackReader reader)
			{
				if (!reader.Read ())
					UnpackFailed ();
				if (reader.IsUnsigned ())
					return reader.ValueUnsigned;
				if (reader.IsUnsigned64 ())
					return reader.ValueUnsigned64;
				UnpackFailed ();
				return 0; // unused
			}

			internal static bool Unpack_Boolean (MsgPackReader reader)
			{
				if (!reader.Read () || !reader.IsBoolean ())
					UnpackFailed ();
				return reader.ValueBoolean;
			}

			internal static float Unpack_Float (MsgPackReader reader)
			{
				if (!reader.Read () || reader.Type != TypePrefixes.Float)
					UnpackFailed ();
				return reader.ValueFloat;
			}

			internal static double Unpack_Double (MsgPackReader reader)
			{
				if (!reader.Read () || reader.Type != TypePrefixes.Double)
					UnpackFailed ();
				return reader.ValueDouble;
			}

			internal static string Unpack_String (MsgPackReader reader)
			{
				if (!reader.Read () || !reader.IsRaw ())
					UnpackFailed ();
				return reader.ReadRawString ();
			}

			internal static void UnpackFailed ()
			{
				throw new FormatException ();
			}
			#endregion
		}
		#endregion
	}
}
