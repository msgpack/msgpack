package org.msgpack.template;

import java.io.IOException;
import java.util.Date;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;

public class DateTemplate implements Template {

	@Override
	public void pack(Packer pk, Object target) throws IOException {
		Date temp = (Date) target;
		pk.packLong(temp.getTime());
	}

	@Override
	public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
		Long temp = pac.unpackLong();
		return new Date(temp);
	}

	@Override
	public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
		Long temp = from.asLong();
		return new Date(temp);
	}

	static public DateTemplate getInstance() {
		return instance;
	}

	static final DateTemplate instance = new DateTemplate();

	static {
		TemplateRegistry.register(Date.class, instance);
	}
}
