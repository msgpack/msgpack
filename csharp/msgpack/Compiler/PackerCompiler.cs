using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Reflection;
using System.Reflection.Emit;
using System.Threading;
using System.Runtime.Serialization;

namespace msgpack.Compiler
{
	public static class PackerCompiler
	{
		static Dictionary<Type, DynamicMethod> CompiledPackMethods;
		static Dictionary<Type, Delegate> PackDelegates;
		static Dictionary<Type, Action<MsgPackWriter, object>> PackWrapperDelegates;

		static Dictionary<Type, MethodInfo> CompiledUnpackMethods;
		static Dictionary<Type, Delegate> UnpackDelegates;
		static Dictionary<Type, Dictionary<string, int>> UnpackFieldMapping;

		static Dictionary<Type, MethodInfo> UserDefinedPackMethods;

		static PackerCompiler ()
		{
			CompiledPackMethods = new Dictionary<Type, DynamicMethod> ();
			PackDelegates = new Dictionary<Type, Delegate> ();
			PackWrapperDelegates = new Dictionary<Type, Action<MsgPackWriter, object>> ();
			UserDefinedPackMethods = new Dictionary<Type, MethodInfo> ();

			CompiledUnpackMethods = new Dictionary<Type, MethodInfo> ();
			UnpackDelegates = new Dictionary<Type, Delegate> ();
			UnpackFieldMapping = new Dictionary<Type, Dictionary<string, int>> ();

			RegisterDefaultUnpackMethods ();
			RegisterUserDefinedMethods ();
		}

		#region Pack Frontend / Compiler
		public static Action<MsgPackWriter,T> GetPackMethod<T> ()
		{
			Delegate d;
			lock (CompiledPackMethods) {
				PackDelegates.TryGetValue (typeof (T), out d);
			}
			if (d == null)
				CreatePackMethod (typeof (T));
			lock (CompiledPackMethods) {
				d = PackDelegates[typeof (T)];
			}
			return (Action<MsgPackWriter,T>)d;
		}

		public static Action<MsgPackWriter, object> GetPackMethod (Type t)
		{
			Action<MsgPackWriter, object> d;
			lock (CompiledPackMethods) {
				PackWrapperDelegates.TryGetValue (t, out d);
			}
			if (d == null)
				CreatePackMethod (t);
			lock (CompiledPackMethods) {
				d = PackWrapperDelegates[t];
			}
			return d;
		}

		static DynamicMethod CreatePackMethod (Type t)
		{
			DynamicMethod methodBuilder;
			lock (CompiledPackMethods) {
				if (CompiledPackMethods.TryGetValue (t, out methodBuilder)) {
					return CompiledPackMethods[t];
				} else {
					methodBuilder = CreateDynamicMethod (typeof (void), new Type[]{typeof (MsgPackWriter), t});
					CompiledPackMethods.Add (t, methodBuilder);
					CreatePackMethod (t, methodBuilder);
					PackDelegates.Add (t, methodBuilder.CreateDelegate (typeof (Action<,>).MakeGenericType (typeof (MsgPackWriter), t)));
					Action<MsgPackWriter, object> wrapper = CreatePackWrapper (t, methodBuilder);
					PackWrapperDelegates.Add (t, wrapper);
				}
			}
			return methodBuilder;
		}

		static void CreatePackMethod (Type t, DynamicMethod methodBuilder)
		{
			if (t == null || methodBuilder == null)
				throw new ArgumentNullException ();
			if (t.IsPrimitive || t.IsInterface)
				throw new NotSupportedException ();

      ILGenerator il = methodBuilder.GetILGenerator();

			Variable arg_writer = Variable.CreateArg (0);
			Variable arg_obj = Variable.CreateArg (1);
			Variable local_i = Variable.CreateLocal (il.DeclareLocal (typeof (int)));

			if (!t.IsValueType) { // null check
				Label notNullLabel = il.DefineLabel ();
				il.EmitLd (arg_obj);
				il.Emit (OpCodes.Brtrue_S, notNullLabel);
				il.EmitLd (arg_writer);
				il.Emit (OpCodes.Call, typeof(MsgPackWriter).GetMethod("WriteNil", new Type[0]));
				il.Emit (OpCodes.Ret);
				il.MarkLabel (notNullLabel);
			}

			MethodInfo udm;
			lock (UserDefinedPackMethods) {
				UserDefinedPackMethods.TryGetValue (t, out udm);
			}
			if (udm != null) {
				il.EmitLd (arg_writer, arg_obj);
				il.Emit (OpCodes.Call, udm);
				goto FinallyProcess;
			}

			if (t.IsArray) {
				EmitArrayWriteProcess (il, t, arg_writer, arg_obj, local_i);
				goto FinallyProcess;
			}

			// MsgPackWriter.WriteMapHeader
			MemberInfo[] members = LookupMembers (t);
			il.EmitLd (arg_writer);
			il.EmitLdc (members.Length);
			il.Emit (OpCodes.Callvirt, typeof (MsgPackWriter).GetMethod("WriteMapHeader", new Type[]{typeof (int)}));

			for (int i = 0; i < members.Length; i ++) {
				MemberInfo m = members[i];
				Type mt = m.GetMemberType ();

				// write field-name
				il.EmitLd (arg_writer);
				il.EmitLdstr (FormatMemberName (m));
				il.EmitLd_True ();
				il.Emit (OpCodes.Call, typeof (MsgPackWriter).GetMethod("Write", new Type[]{typeof (string), typeof (bool)}));

				// write value
				CreatePackMethod_EmitMemberValue (il, arg_writer, arg_obj, m, null, mt, t, methodBuilder);
			}

FinallyProcess:
      il.Emit (OpCodes.Ret);
		}

		static void EmitArrayWriteProcess (ILGenerator il, Type t, Variable var_writer, Variable var_obj, Variable var_loop)
		{
			Type et = t.GetElementType ();
			il.EmitLd (var_writer, var_obj);
			il.Emit (OpCodes.Ldlen);
			il.Emit (OpCodes.Call, typeof(MsgPackWriter).GetMethod("WriteArrayHeader", new Type[]{ typeof(int) }));

			Label beginLabel = il.DefineLabel ();
			Label exprLabel = il.DefineLabel ();

			// for-loop: init loop counter
			il.EmitLdc (0);
			il.EmitSt (var_loop);

			// jump
			il.Emit (OpCodes.Br_S, exprLabel);

			// mark begin-label
			il.MarkLabel (beginLabel);

			// write element
			CreatePackMethod_EmitMemberValue (il, var_writer, var_obj, null, var_loop, et, null, null);

			// increment loop-counter
			il.EmitLd (var_loop);
			il.Emit (OpCodes.Ldc_I4_1);
			il.Emit (OpCodes.Add);
			il.EmitSt (var_loop);

			// mark expression label
			il.MarkLabel (exprLabel);

			// expression
			il.EmitLd (var_loop, var_obj);
			il.Emit (OpCodes.Ldlen);
			il.Emit (OpCodes.Blt_S, beginLabel);
		}

		/// <param name="m">(optional)</param>
		/// <param name="elementIdx">(optional)</param>
		static void CreatePackMethod_EmitMemberValue (ILGenerator il, Variable var_writer, Variable var_obj, MemberInfo m, Variable elementIdx, Type type, Type currentType, DynamicMethod currentMethod)
		{
			MethodInfo mi;
			il.EmitLd (var_writer, var_obj);
			if (m != null)
				il.EmitLdMember (m);
			if (elementIdx != null) {
				il.EmitLd (elementIdx);
				il.Emit (OpCodes.Ldelem, type);
			}
			if (type.IsPrimitive) {
				mi = typeof(MsgPackWriter).GetMethod("Write", new Type[]{type});
			} else {
				if (currentType == type) {
					mi = currentMethod;
				} else {
					lock (UserDefinedPackMethods) {
						UserDefinedPackMethods.TryGetValue (type, out mi);
					}
					if (mi == null)
						mi = CreatePackMethod (type);
				}
			}
			il.Emit (OpCodes.Call, mi);
		}

		static Action<MsgPackWriter, object> CreatePackWrapper (Type t, DynamicMethod packMethod)
		{
			DynamicMethod dm = CreateDynamicMethod (typeof (void), new Type[] {typeof (MsgPackWriter), typeof (object)});
			ILGenerator il = dm.GetILGenerator();
			il.EmitLd (Variable.CreateArg (0), Variable.CreateArg (1));
			il.Emit (OpCodes.Castclass, t);
			il.Emit (OpCodes.Call, packMethod);
			il.Emit (OpCodes.Ret);
			return (Action<MsgPackWriter, object>)dm.CreateDelegate (typeof (Action<MsgPackWriter,object>));
		}
		#endregion

		#region Unpack Frontend / Compiler
		public static Func<MsgPackReader,T> GetUnpackMethod<T> ()
		{
			Delegate d;
			lock (CompiledUnpackMethods) {
				UnpackDelegates.TryGetValue (typeof (T), out d);
			}
			if (d == null)
				CreateUnpackMethod (typeof (T));
			lock (CompiledUnpackMethods) {
				d = UnpackDelegates[typeof (T)];
			}
			return (Func<MsgPackReader,T>)d;
		}

		static MethodInfo CreateUnpackMethod (Type t)
		{
			MethodInfo methodBuilder;
			lock (CompiledUnpackMethods) {
				if (CompiledUnpackMethods.TryGetValue (t, out methodBuilder)) {
					return methodBuilder;
				} else {
					methodBuilder = CreateDynamicMethod (t, new Type[]{typeof (MsgPackReader)});
					CompiledUnpackMethods.Add (t, methodBuilder);
					UnpackFieldMapping.Add (t, new Dictionary<string,int> ());
					if (t.IsArray) {
						CreateUnpackArrayMethod (t, t.GetElementType (), (DynamicMethod)methodBuilder);
					} else {
						CreateUnpackMethod (t, (DynamicMethod)methodBuilder);
					}
					UnpackDelegates.Add (t, ((DynamicMethod)methodBuilder).CreateDelegate (typeof (Func<,>).MakeGenericType (typeof (MsgPackReader), t)));
				}
			}
			return methodBuilder;
		}

		static void CreateUnpackMethod (Type t, DynamicMethod methodBuilder)
		{
			ILGenerator il = methodBuilder.GetILGenerator ();
			MethodInfo failedMethod = typeof (PackerCompiler).GetMethod ("UnpackFailed", BindingFlags.Static | BindingFlags.NonPublic);
			MemberInfo[] members = LookupMembers (t);
			Dictionary<string, int> member_mapping = UnpackFieldMapping[t];
			for (int i = 0; i < members.Length; i ++)
				member_mapping.Add (FormatMemberName (members[i]), i);

			Variable msgpackReader = Variable.CreateArg (0);
			Variable obj = Variable.CreateLocal (il.DeclareLocal (t));
			Variable num_of_fields = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable loop_idx = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable mapping = Variable.CreateLocal (il.DeclareLocal (typeof (Dictionary<string, int>)));
			Variable switch_idx = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable type = Variable.CreateLocal (il.DeclareLocal (typeof (Type)));

			// if (!MsgPackReader.Read()) UnpackFailed ();
			// if (MsgPackReader.Type == TypePrefixes.Nil) return null;
			// if (!MsgPackReader.IsMap ()) UnpackFailed ();
			EmitReadAndTypeCheck (il, msgpackReader, typeof (MsgPackReader).GetMethod ("IsMap"), failedMethod, true);
			
			// type = typeof (T)
			il.Emit (OpCodes.Ldtoken, t);
			il.Emit (OpCodes.Call, typeof(Type).GetMethod ("GetTypeFromHandle"));
			il.EmitSt (type);

			// mapping = LookupMemberMapping (typeof (T))
			il.EmitLd (type);
			il.Emit (OpCodes.Call, typeof (PackerCompiler).GetMethod ("LookupMemberMapping", BindingFlags.Static | BindingFlags.NonPublic));
			il.EmitSt (mapping);

			// object o = FormatterServices.GetUninitializedObject (Type);
			il.EmitLd (type);
			il.Emit (OpCodes.Call, typeof (FormatterServices).GetMethod ("GetUninitializedObject"));
			il.Emit (OpCodes.Castclass, t);
			il.EmitSt (obj);

			// num_of_fields = (int)reader.Length
			il.EmitLd (msgpackReader);
			il.Emit (OpCodes.Call, typeof (MsgPackReader).GetProperty ("Length").GetGetMethod ());
			il.EmitSt (num_of_fields);

			// Loop labels
			Label lblLoopStart = il.DefineLabel ();
			Label lblLoopExpr = il.DefineLabel ();
			
			// i = 0;
			il.EmitLdc (0);
			il.EmitSt (loop_idx);
			il.Emit (OpCodes.Br, lblLoopExpr);
			il.MarkLabel (lblLoopStart);

			/* process */
			// if (!MsgPackReader.Read() || !MsgPackReader.IsRaw()) UnpackFailed();
			EmitReadAndTypeCheck (il, msgpackReader, typeof (MsgPackReader).GetMethod ("IsRaw"), failedMethod, false);

			// MsgPackReader.ReadRawString ()
			// if (!Dictionary.TryGetValue (,)) UnpackFailed();
			Label lbl3 = il.DefineLabel ();
			il.EmitLd (mapping);
			il.EmitLd (msgpackReader);
			il.Emit (OpCodes.Call, typeof (MsgPackReader).GetMethod ("ReadRawString", new Type[0]));
			il.Emit (OpCodes.Ldloca_S, (short)switch_idx.Index);
			il.Emit (OpCodes.Call, typeof (Dictionary<string,int>).GetMethod ("TryGetValue"));
			il.Emit (OpCodes.Brtrue, lbl3);
			il.Emit (OpCodes.Call, failedMethod);
			il.MarkLabel (lbl3);

			// switch
			Label[] switchCases = new Label[members.Length];
			for (int i = 0; i < switchCases.Length; i ++)
				switchCases[i] = il.DefineLabel ();
			Label switchCaseEndLabel = il.DefineLabel ();
			il.EmitLd (switch_idx);
			il.Emit (OpCodes.Switch, switchCases);
			il.Emit (OpCodes.Call, failedMethod);

			for (int i = 0; i < switchCases.Length; i ++) {
				il.MarkLabel (switchCases[i]);
				MemberInfo mi = members[i];
				Type mt = mi.GetMemberType ();
				MethodInfo unpack_method;

				il.EmitLd (obj);
				if (!CompiledUnpackMethods.TryGetValue (mt, out unpack_method)) {
					unpack_method = CreateUnpackMethod (mt);
				}
				il.EmitLd (msgpackReader);
				il.Emit (OpCodes.Call, unpack_method);
				il.EmitStMember (mi);
				il.Emit (OpCodes.Br, switchCaseEndLabel);
			}
			il.MarkLabel (switchCaseEndLabel);

			// i ++
			il.EmitLd (loop_idx);
			il.EmitLdc (1);
			il.Emit (OpCodes.Add);
			il.EmitSt (loop_idx);

			// i < num_of_fields;
			il.MarkLabel (lblLoopExpr);
			il.EmitLd (loop_idx);
			il.EmitLd (num_of_fields);
			il.Emit (OpCodes.Blt, lblLoopStart);
			
			// return
			il.EmitLd (obj);
			il.Emit (OpCodes.Ret);
		}

		static void CreateUnpackArrayMethod (Type arrayType, Type elementType, DynamicMethod methodBuilder)
		{
			ILGenerator il = methodBuilder.GetILGenerator ();
			MethodInfo failedMethod = typeof (PackerCompiler).GetMethod ("UnpackFailed", BindingFlags.Static | BindingFlags.NonPublic);

			Variable msgpackReader = Variable.CreateArg (0);
			Variable obj = Variable.CreateLocal (il.DeclareLocal (arrayType));
			Variable num_of_elements = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable loop_idx = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable type = Variable.CreateLocal (il.DeclareLocal (typeof (Type)));

			// if (!MsgPackReader.Read() || !MsgPackReader.IsArray ()) UnpackFailed ();
			EmitReadAndTypeCheck (il, msgpackReader, typeof (MsgPackReader).GetMethod ("IsArray"), failedMethod, true);

			// type = typeof (T)
			il.Emit (OpCodes.Ldtoken, elementType);
			il.Emit (OpCodes.Call, typeof(Type).GetMethod ("GetTypeFromHandle"));
			il.EmitSt (type);

			// num_of_elements = (int)reader.Length
			il.EmitLd (msgpackReader);
			il.Emit (OpCodes.Call, typeof (MsgPackReader).GetProperty ("Length").GetGetMethod ());
			il.EmitSt (num_of_elements);

			// object o = Array.CreateInstance (Type, Length);
			il.EmitLd (type);
			il.EmitLd (num_of_elements);
			il.Emit (OpCodes.Call, typeof (Array).GetMethod ("CreateInstance", new Type[] {typeof (Type), typeof (int)}));
			il.Emit (OpCodes.Castclass, arrayType);
			il.EmitSt (obj);

			// Unpack element method
			MethodInfo unpack_method;
			lock (CompiledUnpackMethods) {
				if (!CompiledUnpackMethods.TryGetValue (elementType, out unpack_method)) {
					unpack_method = CreateUnpackMethod (elementType);
				}
			}

			// Loop labels
			Label lblLoopStart = il.DefineLabel ();
			Label lblLoopExpr = il.DefineLabel ();
			
			// i = 0;
			il.EmitLdc (0);
			il.EmitSt (loop_idx);
			il.Emit (OpCodes.Br, lblLoopExpr);
			il.MarkLabel (lblLoopStart);

			/* process */
			il.EmitLd (obj, loop_idx);
			il.EmitLd (msgpackReader);
			il.Emit (OpCodes.Call, unpack_method);
			il.Emit (OpCodes.Stelem, elementType);

			// i ++
			il.EmitLd (loop_idx);
			il.EmitLdc (1);
			il.Emit (OpCodes.Add);
			il.EmitSt (loop_idx);

			// i < num_of_fields;
			il.MarkLabel (lblLoopExpr);
			il.EmitLd (loop_idx);
			il.EmitLd (num_of_elements);
			il.Emit (OpCodes.Blt, lblLoopStart);
			
			// return
			il.EmitLd (obj);
			il.Emit (OpCodes.Ret);
		}

		static void EmitReadAndTypeCheck (ILGenerator il, Variable msgpackReader, MethodInfo typeCheckMethod, MethodInfo failedMethod, bool nullCheckAndReturn)
		{
			Label lblFailed = il.DefineLabel ();
			Label lblNullReturn = il.DefineLabel ();
			Label lblPassed = il.DefineLabel ();
			il.EmitLd (msgpackReader);
			il.Emit (OpCodes.Call, typeof (MsgPackReader).GetMethod ("Read"));
			il.Emit (OpCodes.Brfalse_S, lblFailed);
			if (nullCheckAndReturn) {
				il.EmitLd (msgpackReader);
				il.Emit (OpCodes.Call, typeof (MsgPackReader).GetProperty ("Type").GetGetMethod ());
				il.EmitLdc ((int)TypePrefixes.Nil);
				il.Emit (OpCodes.Beq_S, lblNullReturn);
			}
			il.EmitLd (msgpackReader);
			il.Emit (OpCodes.Call, typeCheckMethod);
			il.Emit (OpCodes.Brtrue_S, lblPassed);
			if (nullCheckAndReturn) {
				il.MarkLabel (lblNullReturn);
				il.Emit (OpCodes.Ldnull);
				il.Emit (OpCodes.Ret);
			}
			il.MarkLabel (lblFailed);
			il.Emit (OpCodes.Call, failedMethod);
			il.MarkLabel (lblPassed);
		}
		
		/// <summary>Exception Helper</summary>
		static void UnpackFailed ()
		{
			throw new FormatException ();
		}

		static Dictionary<string, int> LookupMemberMapping (Type t)
		{
			lock (CompiledUnpackMethods) {
				return UnpackFieldMapping[t];
			}
		}

		static void RegisterDefaultUnpackMethods ()
		{
			BindingFlags flags = BindingFlags.Static | BindingFlags.NonPublic;
			MethodInfo mi = typeof (PackerCompiler).GetMethod ("Unpack_Signed", flags);
			CompiledUnpackMethods.Add (typeof (sbyte), mi);
			CompiledUnpackMethods.Add (typeof (short), mi);
			CompiledUnpackMethods.Add (typeof (int), mi);

			mi = typeof (PackerCompiler).GetMethod ("Unpack_Signed64", flags);
			CompiledUnpackMethods.Add (typeof (long), mi);

			mi = typeof (PackerCompiler).GetMethod ("Unpack_Unsigned", flags);
			CompiledUnpackMethods.Add (typeof (byte), mi);
			CompiledUnpackMethods.Add (typeof (ushort), mi);
			CompiledUnpackMethods.Add (typeof (char), mi);
			CompiledUnpackMethods.Add (typeof (uint), mi);

			mi = typeof (PackerCompiler).GetMethod ("Unpack_Unsigned64", flags);
			CompiledUnpackMethods.Add (typeof (ulong), mi);

			mi = typeof (PackerCompiler).GetMethod ("Unpack_Boolean", flags);
			CompiledUnpackMethods.Add (typeof (bool), mi);

			mi = typeof (PackerCompiler).GetMethod ("Unpack_Float", flags);
			CompiledUnpackMethods.Add (typeof (float), mi);

			mi = typeof (PackerCompiler).GetMethod ("Unpack_Double", flags);
			CompiledUnpackMethods.Add (typeof (double), mi);

			mi = typeof (PackerCompiler).GetMethod ("Unpack_String", flags);
			CompiledUnpackMethods.Add (typeof (string), mi);
		}

		static int Unpack_Signed (MsgPackReader reader)
		{
			if (!reader.Read () || !reader.IsSigned ())
				UnpackFailed ();
			return reader.ValueSigned;
		}

		static long Unpack_Signed64 (MsgPackReader reader)
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

		static uint Unpack_Unsigned (MsgPackReader reader)
		{
			if (!reader.Read () || !reader.IsUnsigned ())
				UnpackFailed ();
			return reader.ValueUnsigned;
		}

		static ulong Unpack_Unsigned64 (MsgPackReader reader)
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

		static bool Unpack_Boolean (MsgPackReader reader)
		{
			if (!reader.Read () || !reader.IsBoolean ())
				UnpackFailed ();
			return reader.ValueBoolean;
		}

		static float Unpack_Float (MsgPackReader reader)
		{
			if (!reader.Read () || reader.Type != TypePrefixes.Float)
				UnpackFailed ();
			return reader.ValueFloat;
		}

		static double Unpack_Double (MsgPackReader reader)
		{
			if (!reader.Read () || reader.Type != TypePrefixes.Double)
				UnpackFailed ();
			return reader.ValueDouble;
		}

		static string Unpack_String (MsgPackReader reader)
		{
			if (!reader.Read () || !reader.IsRaw ())
				UnpackFailed ();
			return reader.ReadRawString ();
		}
		#endregion

		#region User Defined Packer/Unpackers
		static void RegisterUserDefinedMethods ()
		{
			BindingFlags flags = BindingFlags.Static | BindingFlags.NonPublic;
			Type type = typeof (PackerCompiler);
			object[][] list = new object[][] {
				new object[] {typeof (string), "PackString"}
			};
			for (int i = 0; i < list.Length; i ++)
				UserDefinedPackMethods.Add ((Type)list[i][0], type.GetMethod ((string)list[i][1], flags));
		}

		static void PackString (MsgPackWriter writer, string x)
		{
			writer.Write (x);
		}
		#endregion

		#region Misc
		static int _dynamicMethodIdx = 0;
		static DynamicMethod CreateDynamicMethod (Type returnType, Type[] parameterTypes)
		{
			string name = "_" + Interlocked.Increment (ref _dynamicMethodIdx).ToString ();
			return new DynamicMethod (name, returnType, parameterTypes, true);
		}

		static MemberInfo[] LookupMembers (Type t)
		{
			BindingFlags baseFlags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
			List<MemberInfo> list = new List<MemberInfo> ();
			list.AddRange (t.GetFields (baseFlags));
			//list.AddRange (t.GetProperties (baseFlags)); // TODO:
			return list.ToArray ();
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

		static Type GetMemberType (this MemberInfo mi)
		{
			if (mi.MemberType == MemberTypes.Field)
				return ((FieldInfo)mi).FieldType;
			if (mi.MemberType == MemberTypes.Property)
				return ((PropertyInfo)mi).PropertyType;
			throw new ArgumentException ();
		}
		#endregion
	}
}
