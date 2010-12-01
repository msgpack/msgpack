package org.msgpack.buffer;

import org.msgpack.*;
import org.msgpack.object.*;
import java.io.*;
import java.util.*;
import java.util.concurrent.*;
import java.net.*;
import junit.framework.*;
import org.junit.Test;

public class VectoredByteBufferTest extends TestCase {
	public VectoredByteBufferTest() {
	}

	@Test
	public void testIO() throws Exception {
		VectoredByteBuffer v = new VectoredByteBuffer();
		ByteArrayOutputStream bo = new ByteArrayOutputStream();
		byte[] ref = new byte[40];
		byte[] copy = new byte[3];
		ref[0] = 10;
		ref[1] = 20;
		ref[2] = 30;
		copy[0] = 40;
		copy[1] = 50;
		copy[2] = 60;

		byte[][] src = new byte[][] {
			copy, ref, ref, copy, ref, copy, copy, ref
		};

		for(byte[] s : src) {
			bo.write(s);
			v.write(s);
		}

		ByteArrayOutputStream check = new ByteArrayOutputStream();
		v.writeTo(check);

		assertEquals(bo.size(), check.size());
		assertTrue(Arrays.equals(bo.toByteArray(), check.toByteArray()));
	}
}

