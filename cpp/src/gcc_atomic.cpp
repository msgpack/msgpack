#if defined(__GNUC__) && ((__GNUC__*10 + __GNUC_MINOR__) < 41)

#include "gcc_atomic.h"
#include <bits/atomicity.h>

int _msgpack_sync_decr_and_fetch(volatile _msgpack_atomic_counter_t* ptr)
{
	return  __gnu_cxx::__exchange_and_add(ptr, -1);
}

int _msgpack_sync_incr_and_fetch(volatile _msgpack_atomic_counter_t* ptr)
{
	return  __gnu_cxx::__exchange_and_add(ptr, 1);
}


#endif // old gcc workaround
