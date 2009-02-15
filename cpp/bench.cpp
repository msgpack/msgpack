#include <msgpack/unpack.hpp>
#include <msgpack/pack.hpp>
#include <string.h>
#include <sys/time.h>
#include <iostream>
#include <stdexcept>
#include <string>

static const unsigned int TASK_INT_NUM = 1<<24;
static const unsigned int TASK_STR_LEN = 1<<15;
//static const unsigned int TASK_INT_NUM = 1<<22;
//static const unsigned int TASK_STR_LEN = 1<<13;
static const char* TASK_STR_PTR;


class simple_timer {
public:
	void reset() { gettimeofday(&m_timeval, NULL); }
	void show_stat(size_t bufsz)
	{
		struct timeval endtime;
		gettimeofday(&endtime, NULL);
		double sec = (endtime.tv_sec - m_timeval.tv_sec)
			+ (double)(endtime.tv_usec - m_timeval.tv_usec) / 1000 / 1000;
		std::cout << sec << " sec" << std::endl;
		std::cout << (double(bufsz)/1024/1024) << " MB" << std::endl;
		std::cout << (bufsz/sec/1000/1000*8) << " Mbps" << std::endl;
	}
private:
	timeval m_timeval;
};


class simple_buffer {
public:
	static const size_t DEFAULT_INITIAL_SIZE = 32*1024;//512*1024*1024*2;

	simple_buffer(size_t initial_size = DEFAULT_INITIAL_SIZE) :
		m_storage((char*)malloc(initial_size)),
		m_allocated(initial_size),
		m_used(0)
	{
		if(!m_storage) { throw std::bad_alloc(); }
	}

	~simple_buffer()
	{
		free(m_storage);
	}

public:
	inline void write(const char* buf, size_t len)
	{
		if(m_allocated - m_used < len) {
			expand_buffer(len);
		}
		memcpy(m_storage + m_used, buf, len);
		m_used += len;
	}

	void clear()
	{
		m_used = 0;
	}

private:
	void expand_buffer(size_t req)
	{
		size_t nsize = m_allocated * 2;
		size_t at_least = m_used + req;
		while(nsize < at_least) { nsize *= 2; }
		char* tmp = (char*)realloc(m_storage, nsize);
		if(!tmp) { throw std::bad_alloc(); }
		m_storage = tmp;
		m_allocated = nsize;
	}

public:
	size_t size() const { return m_used; }
	const char* data() const { return m_storage; }

private:
	char* m_storage;
	size_t m_allocated;
	size_t m_used;
};


void bench_msgpack_int()
{
	simple_buffer buf;
	simple_timer timer;

	std::cout << "----" << std::endl;
	std::cout << "pack integer" << std::endl;

	timer.reset();
	{
		msgpack::packer<simple_buffer> pk(buf);
		pk.pack_array(TASK_INT_NUM);
		for(unsigned int i=0; i < TASK_INT_NUM; ++i) {
			pk.pack_unsigned_int(i);
		}
	}
	timer.show_stat(buf.size());


	std::cout << "----" << std::endl;
	std::cout << "unpack integer" << std::endl;

	msgpack::zone z;
	msgpack::object obj;

	timer.reset();
	{
		obj = msgpack::unpack(buf.data(), buf.size(), z);
	}
	timer.show_stat(buf.size());

	/*
	std::cout << "----" << std::endl;
	std::cout << "dynamic pack integer" << std::endl;

	buf.clear();

	timer.reset();
	msgpack::pack(buf, obj);
	timer.show_stat(buf.size());
	*/
}

void bench_msgpack_str()
{
	simple_buffer buf;
	simple_timer timer;

	std::cout << "----" << std::endl;
	std::cout << "pack string" << std::endl;

	timer.reset();
	{
		msgpack::packer<simple_buffer> pk(buf);
		pk.pack_array(TASK_STR_LEN);
		for(unsigned int i=0; i < TASK_STR_LEN; ++i) {
			pk.pack_raw(i);
			pk.pack_raw_body(TASK_STR_PTR, i);
		}
	}
	timer.show_stat(buf.size());


	std::cout << "----" << std::endl;
	std::cout << "unpack string" << std::endl;

	msgpack::zone z;
	msgpack::object obj;

	timer.reset();
	{
		obj = msgpack::unpack(buf.data(), buf.size(), z);
	}
	timer.show_stat(buf.size());


	/*
	std::cout << "----" << std::endl;
	std::cout << "dynamic pack string" << std::endl;

	buf.clear();

	timer.reset();
	msgpack::pack(buf, obj);
	timer.show_stat(buf.size());
	*/
}

int main(void)
{
	char* str = (char*)malloc(TASK_STR_LEN);
	memset(str, 'a', TASK_STR_LEN);
	TASK_STR_PTR = str;

	bench_msgpack_int();
	bench_msgpack_str();

	return 0;
}

