#include "msgpack/unpack.hpp"
#include "unpack_context.hpp"
#include <stdlib.h>

namespace msgpack {

struct unpacker::context {
	context(zone& z)
	{
		msgpack_unpacker_init(&m_ctx);
		m_ctx.user = &z;
	}

	~context() { }

	int execute(const void* data, size_t len, size_t* off)
	{
		return msgpack_unpacker_execute(&m_ctx, (const char*)data, len, off);
	}

	object_class* data()
	{
		return msgpack_unpacker_data(&m_ctx);
	}

	void reset()
	{
		zone* z = m_ctx.user;
		msgpack_unpacker_init(&m_ctx);
		m_ctx.user = z;
	}

private:
	msgpack_unpacker m_ctx;

private:
	context();
	context(const context&);
};


unpacker::unpacker(zone& z) :
	m_ctx(new context(z)),
	m_zone(z),
	m_finished(false)
{ }


unpacker::~unpacker() { delete m_ctx; }


size_t unpacker::execute(const void* data, size_t len, size_t off)
{
	int ret = m_ctx->execute(data, len, &off);
	if(ret < 0) {
		throw unpack_error("parse error");
	} else if(ret > 0) {
		m_finished = true;
		return off;
	} else {
		m_finished = false;
		return off;
	}
}


object unpacker::data()
{
	return object(m_ctx->data());
}


void unpacker::reset()
{
	m_ctx->reset();
}


object unpacker::unpack(const void* data, size_t len, zone& z)
{
	context ctx(z);
	size_t off = 0;
	int ret = ctx.execute(data, len, &off);
	if(ret < 0) {
		throw unpack_error("parse error");
	} else if(ret == 0) {
		throw unpack_error("insufficient bytes");
	} else if(off < len) {
		throw unpack_error("extra bytes");
	}
	return ctx.data();
}


}  // namespace msgpack

