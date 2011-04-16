using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Reflection.Emit;

namespace msgpack.Compiler
{
	public class Variable
	{
		Variable (VariableType type, int index)
		{
			this.VarType = type;
			this.Index = index;
		}

		public static Variable CreateLocal (LocalBuilder local)
		{
			return new Variable (VariableType.Local, local.LocalIndex);
		}

		public static Variable CreateArg (int idx)
		{
			return new Variable (VariableType.Arg, idx);
		}

		public VariableType VarType { get; set; }
		public int Index { get; set; }
	}
}
