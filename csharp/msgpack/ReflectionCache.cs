using System;
using System.Collections.Generic;

namespace msgpack
{
	public static class ReflectionCache
	{
		static Dictionary<Type, ReflectionCacheEntry> _cache;

		static ReflectionCache ()
		{
			_cache = new Dictionary<Type,ReflectionCacheEntry> ();
		}

		public static ReflectionCacheEntry Lookup (Type type)
		{
			ReflectionCacheEntry entry;
			lock (_cache) {
				if (_cache.TryGetValue (type, out entry))
					return entry;
			}

			entry = new ReflectionCacheEntry (type);
			lock (_cache) {
				_cache[type] = entry;
			}
			return entry;
		}

		public static void RemoveCache (Type type)
		{
			lock (_cache) {
				_cache.Remove (type);
			}
		}

		public static void Clear ()
		{
			lock (_cache) {
				_cache.Clear ();
			}
		}
	}
}
