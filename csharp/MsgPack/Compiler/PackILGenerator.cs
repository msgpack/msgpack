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
using System.Reflection;
using System.Reflection.Emit;
using System.Runtime.Serialization;

namespace MsgPack.Compiler
{
	static class PackILGenerator
	{
		#region Pack IL Generator
		public static void EmitPackCode (Type type, MethodInfo mi, ILGenerator il,
			Func<Type,MemberInfo[]> targetMemberSelector,
			Func<MemberInfo,string> memberNameFormatter,
			Func<Type, MethodInfo> lookupPackMethod)
		{
			if (type.IsPrimitive || type.IsInterface)
				throw new NotSupportedException ();

			Variable arg_writer = Variable.CreateArg (0);
			Variable arg_obj = Variable.CreateArg (1);
			Variable local_i = Variable.CreateLocal (il.DeclareLocal (typeof (int)));

			if (!type.IsValueType) { // null check
				Label notNullLabel = il.DefineLabel ();
				il.EmitLd (arg_obj);
				il.Emit (OpCodes.Brtrue_S, notNullLabel);
				il.EmitLd (arg_writer);
				il.Emit (OpCodes.Call, typeof(MsgPackWriter).GetMethod("WriteNil", new Type[0]));
				il.Emit (OpCodes.Ret);
				il.MarkLabel (notNullLabel);
			}

			if (type.IsArray) {
				EmitPackArrayCode (mi, il, type, arg_writer, arg_obj, local_i, lookupPackMethod);
				goto FinallyProcess;
			}

			// MsgPackWriter.WriteMapHeader
			MemberInfo[] members = targetMemberSelector (type);
			il.EmitLd (arg_writer);
			il.EmitLdc (members.Length);
			il.Emit (OpCodes.Callvirt, typeof (MsgPackWriter).GetMethod("WriteMapHeader", new Type[]{typeof (int)}));

			for (int i = 0; i < members.Length; i ++) {
				MemberInfo m = members[i];
				Type mt = m.GetMemberType ();

				// write field-name
				il.EmitLd (arg_writer);
				il.EmitLdstr (memberNameFormatter (m));
				il.EmitLd_True ();
				il.Emit (OpCodes.Call, typeof (MsgPackWriter).GetMethod("Write", new Type[]{typeof (string), typeof (bool)}));

				// write value
				EmitPackMemberValueCode (mt, il, arg_writer, arg_obj, m, null, type, mi, lookupPackMethod);
			}

FinallyProcess:
      il.Emit (OpCodes.Ret);
		}

		static void EmitPackArrayCode (MethodInfo mi, ILGenerator il, Type t, Variable var_writer, Variable var_obj, Variable var_loop, Func<Type, MethodInfo> lookupPackMethod)
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
			EmitPackMemberValueCode (et, il, var_writer, var_obj, null, var_loop, t, mi, lookupPackMethod);

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
		static void EmitPackMemberValueCode (Type type, ILGenerator il, Variable var_writer, Variable var_obj,
			MemberInfo m, Variable elementIdx, Type currentType, MethodInfo currentMethod, Func<Type, MethodInfo> lookupPackMethod)
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
					mi = lookupPackMethod (type);
				}
			}
			il.Emit (OpCodes.Call, mi);
		}
		#endregion

		#region Unpack IL Generator
		public static void EmitUnpackCode (Type type, MethodInfo mi, ILGenerator il,
			Func<Type,MemberInfo[]> targetMemberSelector,
			Func<MemberInfo,string> memberNameFormatter,
			Func<Type, MethodInfo> lookupUnpackMethod,
			Func<Type, IDictionary<string,int>> lookupMemberMapping,
			MethodInfo lookupMemberMappingMethod)
		{
			if (type.IsArray) {
				EmitUnpackArrayCode (type, mi, il, targetMemberSelector, memberNameFormatter, lookupUnpackMethod);
			} else {
				EmitUnpackMapCode (type, mi, il, targetMemberSelector, memberNameFormatter, lookupUnpackMethod, lookupMemberMapping, lookupMemberMappingMethod);
			}
		}

		static void EmitUnpackMapCode (Type type, MethodInfo mi, ILGenerator il,
			Func<Type,MemberInfo[]> targetMemberSelector,
			Func<MemberInfo,string> memberNameFormatter,
			Func<Type, MethodInfo> lookupUnpackMethod,
			Func<Type, IDictionary<string,int>> lookupMemberMapping,
			MethodInfo lookupMemberMappingMethod)
		{
			MethodInfo failedMethod = typeof (PackILGenerator).GetMethod ("UnpackFailed", BindingFlags.Static | BindingFlags.NonPublic);
			MemberInfo[] members = targetMemberSelector (type);
			IDictionary<string, int> member_mapping = lookupMemberMapping (type);
			for (int i = 0; i < members.Length; i ++)
				member_mapping.Add (memberNameFormatter (members[i]), i);

			Variable msgpackReader = Variable.CreateArg (0);
			Variable obj = Variable.CreateLocal (il.DeclareLocal (type));
			Variable num_of_fields = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable loop_idx = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable mapping = Variable.CreateLocal (il.DeclareLocal (typeof (IDictionary<string, int>)));
			Variable switch_idx = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable var_type = Variable.CreateLocal (il.DeclareLocal (typeof (Type)));

			// if (!MsgPackReader.Read()) UnpackFailed ();
			// if (MsgPackReader.Type == TypePrefixes.Nil) return null;
			// if (!MsgPackReader.IsMap ()) UnpackFailed ();
			EmitUnpackReadAndTypeCheckCode (il, msgpackReader, typeof (MsgPackReader).GetMethod ("IsMap"), failedMethod, true);
			
			// type = typeof (T)
			il.Emit (OpCodes.Ldtoken, type);
			il.Emit (OpCodes.Call, typeof(Type).GetMethod ("GetTypeFromHandle"));
			il.EmitSt (var_type);

			// mapping = LookupMemberMapping (typeof (T))
			il.EmitLd (var_type);
			il.Emit (OpCodes.Call, lookupMemberMappingMethod);
			il.EmitSt (mapping);

			// object o = FormatterServices.GetUninitializedObject (Type);
			il.EmitLd (var_type);
			il.Emit (OpCodes.Call, typeof (FormatterServices).GetMethod ("GetUninitializedObject"));
			il.Emit (OpCodes.Castclass, type);
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
			EmitUnpackReadAndTypeCheckCode (il, msgpackReader, typeof (MsgPackReader).GetMethod ("IsRaw"), failedMethod, false);

			// MsgPackReader.ReadRawString ()
			// if (!Dictionary.TryGetValue (,)) UnpackFailed();
			Label lbl3 = il.DefineLabel ();
			il.EmitLd (mapping);
			il.EmitLd (msgpackReader);
			il.Emit (OpCodes.Call, typeof (MsgPackReader).GetMethod ("ReadRawString", new Type[0]));
			il.Emit (OpCodes.Ldloca_S, (byte)switch_idx.Index);
			il.Emit (OpCodes.Callvirt, typeof (IDictionary<string,int>).GetMethod ("TryGetValue"));
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
				MemberInfo minfo = members[i];
				Type mt = minfo.GetMemberType ();
				MethodInfo unpack_method = lookupUnpackMethod (mt);
				il.EmitLd (obj);
				il.EmitLd (msgpackReader);
				il.Emit (OpCodes.Call, unpack_method);
				il.EmitStMember (minfo);
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

		static void EmitUnpackArrayCode (Type arrayType, MethodInfo mi, ILGenerator il,
			Func<Type,MemberInfo[]> targetMemberSelector,
			Func<MemberInfo,string> memberNameFormatter,
			Func<Type, MethodInfo> lookupUnpackMethod)
		{
			Type elementType = arrayType.GetElementType ();
			MethodInfo failedMethod = typeof (PackILGenerator).GetMethod ("UnpackFailed", BindingFlags.Static | BindingFlags.NonPublic);

			Variable msgpackReader = Variable.CreateArg (0);
			Variable obj = Variable.CreateLocal (il.DeclareLocal (arrayType));
			Variable num_of_elements = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable loop_idx = Variable.CreateLocal (il.DeclareLocal (typeof (int)));
			Variable type = Variable.CreateLocal (il.DeclareLocal (typeof (Type)));

			// if (!MsgPackReader.Read() || !MsgPackReader.IsArray ()) UnpackFailed ();
			EmitUnpackReadAndTypeCheckCode (il, msgpackReader, typeof (MsgPackReader).GetMethod ("IsArray"), failedMethod, true);

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
			MethodInfo unpack_method = lookupUnpackMethod (elementType);

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

		static void EmitUnpackReadAndTypeCheckCode (ILGenerator il, Variable msgpackReader, MethodInfo typeCheckMethod, MethodInfo failedMethod, bool nullCheckAndReturn)
		{
			Label lblFailed = il.DefineLabel ();
			Label lblNullReturn = nullCheckAndReturn ? il.DefineLabel () : default(Label);
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
			il.Emit (OpCodes.Br, lblFailed);
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
		internal static void UnpackFailed ()
		{
			throw new FormatException ();
		}
		#endregion

		#region Misc
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
