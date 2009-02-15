#include "unpack.h"
#include "unpack_context.h"
#include <stdlib.h>

msgpack_unpack_t* msgpack_unpack_new(void)
{
	msgpack_unpacker* ctx;
	ctx = (msgpack_unpacker*)calloc(1, sizeof(msgpack_unpacker));
	if(ctx == NULL) { return NULL; }
	msgpack_unpacker_init(ctx);
	return (msgpack_unpack_t*)ctx;
}

void msgpack_unpack_free(msgpack_unpack_t* ctx)
{
	free((msgpack_unpacker*)ctx);
}

int msgpack_unpack_execute(msgpack_unpack_t* ctx, const char* data, size_t len, size_t* off)
{
	return msgpack_unpacker_execute(
			(msgpack_unpacker*)ctx,
			data, len, off);
}

void* msgpack_unpack_data(msgpack_unpack_t* ctx)
{
	return msgpack_unpacker_data((msgpack_unpacker*)ctx);
}

