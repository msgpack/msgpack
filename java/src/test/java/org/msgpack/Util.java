package org.msgpack;

import static org.junit.Assert.assertEquals;

import java.io.ByteArrayInputStream;
import java.util.Iterator;

public class Util {

	public static MessagePackObject unpackOne(byte[] bytes) {
		ByteArrayInputStream in = new ByteArrayInputStream(bytes);
		Unpacker pac = new Unpacker(in);
		Iterator<MessagePackObject> it = pac.iterator();
		assertEquals(true, it.hasNext());
		MessagePackObject obj = it.next();
		assertEquals(false, it.hasNext());
		return obj;
	}
}
