package org.msgpack.util.codegen;

import java.io.IOException;
import java.nio.ByteBuffer;

import org.msgpack.CustomMessage;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

public class ByteBufferTemplate implements Template {
	private ByteBufferTemplate() {
	}

	public void pack(Packer pk, Object target) throws IOException {
		byte[] bytes = byteBufferToByteArray((ByteBuffer) target);
		pk.packByteArray(bytes);
	}

	public Object unpack(Unpacker pac) throws IOException, MessageTypeException {
		byte[] bytes = pac.unpackByteArray();
		return ByteBuffer.wrap(bytes);
	}

	public Object convert(MessagePackObject from) throws MessageTypeException {
		byte[] b = from.asByteArray();
		return ByteBuffer.wrap(b);
	}

	private static byte[] byteBufferToByteArray(ByteBuffer b) {
		if (b.hasArray() && b.position() == 0 && b.arrayOffset() == 0
				&& b.remaining() == b.capacity()) {
			return b.array();
		} else {
			int len = b.remaining();
			byte[] ret = new byte[len];
			System.arraycopy(b.array(), b.arrayOffset() + b.position(), ret, 0, len);
			return ret;
		}
	}

	static public ByteBufferTemplate getInstance() {
		return instance;
	}

	static final ByteBufferTemplate instance = new ByteBufferTemplate();

	static {
		CustomMessage.register(ByteBuffer.class, instance);
	}
}
