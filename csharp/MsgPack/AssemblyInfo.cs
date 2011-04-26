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

using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

[assembly: AssemblyTitle ("MsgPack")]
[assembly: AssemblyProduct ("MsgPack")]
[assembly: AssemblyDescription ("MessagePack Serializer for .NET")]
[assembly: AssemblyCopyright ("Copyright © 2011 Kazuki Oikawa")]

[assembly: ComVisible (false)]
[assembly: AssemblyVersion ("0.1.*")]
[assembly: InternalsVisibleTo (MsgPack.CompiledPacker.MethodBuilderPacker.AssemblyName)]
