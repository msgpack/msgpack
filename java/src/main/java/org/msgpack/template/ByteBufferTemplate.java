package org.msgpack.template;

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
		pk.packByteBuffer((ByteBuffer)target);
	}

	public Object unpack(Unpacker pac) throws IOException, MessageTypeException {
		return pac.unpackByteBuffer();
	}

	public Object convert(MessagePackObject from) throws MessageTypeException {
		byte[] b = from.asByteArray();
		return ByteBuffer.wrap(b);
	}

	static public ByteBufferTemplate getInstance() {
		return instance;
	}

	static final ByteBufferTemplate instance = new ByteBufferTemplate();

	static {
		CustomMessage.register(ByteBuffer.class, instance);
	}
}
