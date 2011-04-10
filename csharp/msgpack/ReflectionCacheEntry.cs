using System;
using System.Collections.Generic;
using System.Reflection;

namespace msgpack
{
	public class ReflectionCacheEntry
	{
		const BindingFlags FieldBindingFlags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.GetField | BindingFlags.SetField;
		
		public ReflectionCacheEntry (Type t)
		{
			FieldInfo[] fields = t.GetFields (FieldBindingFlags);
			IDictionary<string, FieldInfo> map = new Dictionary<string, FieldInfo> (fields.Length);
			for (int i = 0; i < fields.Length; i ++) {
				FieldInfo f = fields[i];
				string name = f.Name;
				int pos;
				if (name[0] == '<' && (pos = name.IndexOf ('>')) > 1)
					name = name.Substring (1, pos - 1); // Auto-Property (\<.+\>) <ab>
				map[name] = f;
			}
			FieldMap = map;
		}

		public IDictionary<string, FieldInfo> FieldMap { get; private set; }
	}
}
