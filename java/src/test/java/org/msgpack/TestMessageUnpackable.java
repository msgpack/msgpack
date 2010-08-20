package org.msgpack;

import org.msgpack.*;
import java.io.*;
import java.util.*;
import java.math.BigInteger;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestMessageUnpackable {
	@Test
	public void testImage() throws Exception {
		Image src = new Image();
		src.title = "msgpack";
		src.uri = "http://msgpack.org/";
		src.width = 2560;
		src.height = 1600;
		src.size = 4096000;

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		src.messagePack(new Packer(out));

		Image dst = new Image();

		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);

		dst.messageUnpack(pac);

		assertEquals(src, dst);
	}
}

