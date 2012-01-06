using System;
using System.Collections;
using System.Collections.Generic;
using System.Reflection;
using System.Reflection.Emit;

namespace MsgPack.Compiler
{
    public static class DictionaryILGenerator
    {
        /// <summary>
        /// Emits IL code to pack a Map based on IDictionary.
        /// </summary>
        /// <param name="currentMethod">Current method info.</param>
        /// <param name="gen">il buffer/generator</param>
        /// <param name="type">Current type</param>
        /// <param name="arg_writer">packer object</param>
        /// <param name="arg_obj">current object</param>
        /// <param name="lookupPackMethod">dictionary to look for methods</param>
        public static void EmitPackIL(MethodInfo currentMethod, ILGenerator gen, Type type, Variable arg_writer, Variable arg_obj, Func<Type, MethodInfo> lookupPackMethod)
        {
            Type keyType = type.GetGenericArguments()[0];
            Type valueType = type.GetGenericArguments()[1];
            Type keyValuePairType = typeof(KeyValuePair<,>).MakeGenericType(keyType, valueType);

            // Preparing Reflection instances
            MethodInfo getCount = typeof(ICollection<>).MakeGenericType(keyValuePairType).GetMethod(
                "get_Count",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{
            },
                null
                );
            MethodInfo writeMapHeader = typeof(MsgPackWriter).GetMethod(
                "WriteMapHeader",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{
            typeof(Int32)
            },
                null
                );
            MethodInfo getEnumerator = typeof(IEnumerable<>).MakeGenericType(keyValuePairType).GetMethod(
                "GetEnumerator",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{
            },
                null
                );
            MethodInfo getCurrent = typeof(IEnumerator<>).MakeGenericType(keyValuePairType).GetMethod(
                "get_Current",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{ },
                null
                );
            MethodInfo getKey = keyValuePairType.GetMethod(
                "get_Key",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{ },
                null
                );
  
            MethodInfo getValue = keyValuePairType.GetMethod(
                "get_Value",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{ },
                null
                );
            MethodInfo moveNext = typeof(IEnumerator).GetMethod(
                "MoveNext",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{ },
                null
                );
            MethodInfo dispose = typeof(IDisposable).GetMethod(
                "Dispose",
                BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
                null,
                new Type[]{ },
                null
                );

            // Preparing locals
            LocalBuilder keyValuepair = gen.DeclareLocal(keyValuePairType);
            LocalBuilder enumerator = gen.DeclareLocal(typeof(System.Collections.Generic.IEnumerator<>).MakeGenericType(keyValuePairType));
            Variable localValue = Variable.CreateLocal(gen.DeclareLocal(valueType));

            // Preparing labels
            Label getNext = gen.DefineLabel();
            Label work = gen.DefineLabel();
            Label end = gen.DefineLabel();
            Label endFinally = gen.DefineLabel();

            // Writing body
            gen.Emit(OpCodes.Ldarg_0);
            gen.Emit(OpCodes.Ldarg_1);
            gen.Emit(OpCodes.Callvirt, getCount);
            gen.Emit(OpCodes.Callvirt, writeMapHeader);
            gen.Emit(OpCodes.Ldarg_1);
            gen.Emit(OpCodes.Callvirt, getEnumerator);
            gen.Emit(OpCodes.Stloc_1);
            gen.BeginExceptionBlock();
            gen.Emit(OpCodes.Br_S, getNext);
            gen.MarkLabel(work);
            gen.Emit(OpCodes.Ldloc_1);
            gen.Emit(OpCodes.Callvirt, getCurrent);
            gen.Emit(OpCodes.Stloc_0);
            gen.Emit(OpCodes.Ldarg_0);
            gen.Emit(OpCodes.Ldloca_S, 0);
            gen.Emit(OpCodes.Call, getKey);
            EmitPack(gen, keyType, type, currentMethod, lookupPackMethod);
            gen.Emit(OpCodes.Ldarg_0);
            gen.Emit(OpCodes.Ldloca_S, 0);
            gen.Emit(OpCodes.Call, getValue);
            EmitPack(gen, valueType, type, currentMethod, lookupPackMethod);
            gen.MarkLabel(getNext);
            gen.Emit(OpCodes.Ldloc_1);
            gen.Emit(OpCodes.Callvirt, moveNext);
            gen.Emit(OpCodes.Brtrue_S, work);
            gen.Emit(OpCodes.Leave_S, end);
            gen.BeginFinallyBlock();
            gen.Emit(OpCodes.Ldloc_1);
            gen.Emit(OpCodes.Brfalse_S, endFinally);
            gen.Emit(OpCodes.Ldloc_1);
            gen.Emit(OpCodes.Callvirt, dispose);
            gen.MarkLabel(endFinally);
            gen.Emit(OpCodes.Endfinally);
            gen.EndExceptionBlock();
            gen.MarkLabel(end);
            gen.Emit(OpCodes.Ret); // <- Yep, I know there is a Ret in the calling function.
            // finished
        }

        public static void EmitUnpackIL(Type mapType, MethodInfo mi, ILGenerator il,
    Func<Type, MemberInfo[]> targetMemberSelector,
    Func<MemberInfo, string> memberNameFormatter,
    Func<Type, MethodInfo> lookupUnpackMethod)
        {

            // References
            var failedMethod = typeof(PackILGenerator).GetMethod("UnpackFailed", BindingFlags.Static | BindingFlags.NonPublic);
            // Variables
            var obj = Variable.CreateLocal(il.DeclareLocal(mapType));
            var msgpackReader = Variable.CreateArg(0);
            var var_type = Variable.CreateLocal(il.DeclareLocal(typeof(Type)));
            var num_of_fields = Variable.CreateLocal(il.DeclareLocal(typeof(int)));

            PackILGenerator.EmitUnpackReadAndTypeCheckCode(il, msgpackReader, typeof(MsgPackReader).GetMethod("IsMap"), failedMethod, true);

            // num_of_fields = (int)reader.Length
            il.EmitLd(msgpackReader);
            il.Emit(OpCodes.Call, typeof(MsgPackReader).GetProperty("Length").GetGetMethod());
            il.EmitSt(num_of_fields);

            // mapType
            il.EmitLd(num_of_fields);
            il.Emit(OpCodes.Newobj, mapType.GetConstructor(new Type[] { typeof(int) }));
            il.EmitSt(obj);

            // Problems with this: It only reads empty dictionaries.

            // return
            il.EmitLd(obj);
            il.Emit(OpCodes.Ret);
        }

        public static void EmitPack(ILGenerator gen, Type type, Type currentType, MethodInfo currentMethod, Func<Type, MethodInfo> lookupPackMethod)
        {
            MethodInfo packerMethod=null;
            if (type.IsPrimitive || type == typeof(Guid))
            {
                packerMethod = typeof(MsgPackWriter).GetMethod("Write", new Type[] { type });
            }
            if(packerMethod == null)
            {
                if (currentType == type)
                {
                    packerMethod = currentMethod;
                }
                else
                {
                    packerMethod = lookupPackMethod(type);
                }
            }
            gen.Emit(OpCodes.Call, packerMethod);
        }
    }
}
