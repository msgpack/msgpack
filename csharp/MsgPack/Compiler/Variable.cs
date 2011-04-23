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

using System.Reflection.Emit;

namespace MsgPack.Compiler
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
