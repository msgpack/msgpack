package org.msgpack;

import org.msgpack.*;
import org.msgpack.object.*;
import org.msgpack.annotation.*;
import static org.msgpack.Templates.*;

import java.io.*;
import java.util.*;
import java.math.BigInteger;

import org.junit.Test;
import junit.framework.TestCase;

public class TestAnnotations extends TestCase {

	@MessagePackMessage
	public static class MyClassVersion1 {
		// required field, not nullable.
		public String name;

		// required and nullable field.
		@MessagePackNullable
		public String nickname;
	}


	@MessagePackMessage
	public static class MyClassVersion2 {
		public String name;

		@MessagePackNullable
		public String nickname;

		// adds an optional field on version 2.
		@MessagePackOptional
		public int age = -1;
	}


	@MessagePackMessage
	public static class MyClassVersion3 {
		public String name;

		@MessagePackNullable
		public String nickname;

		// adds required fields on version 3, then
		// this class is NOT compatible with version 1.
		public int age;

		// optional field is nullable.
		@MessagePackOptional
		public String school;
	}


	@Test
	public void testBackwardCompatibility() throws Exception {
		MyClassVersion1 v1 = new MyClassVersion1();
		v1.name = "Sadayuki Furuhashi";
		v1.nickname = "frsyuki";

		byte[] bytes = MessagePack.pack(v1);

		MyClassVersion2 v2 = MessagePack.unpack(bytes, MyClassVersion2.class);

		assertEquals(v1.name, v2.name);
		assertEquals(v1.nickname, v2.nickname);
		assertEquals(v2.age, -1);
	}

	@Test
	public void testForwardCompatibility() throws Exception {
		MyClassVersion2 v2 = new MyClassVersion2();
		v2.name = "Sadayuki Furuhashi";
		v2.nickname = "frsyuki";
		v2.age = 23;

		byte[] bytes = MessagePack.pack(v2);

		MyClassVersion1 v1 = MessagePack.unpack(bytes, MyClassVersion1.class);

		assertEquals(v2.name, v1.name);
		assertEquals(v2.nickname, v1.nickname);
	}

	@Test
	public void testNullFields01() throws Exception {
		MyClassVersion1 src = new MyClassVersion1();
		src.name = "Sadayuki Furuhashi";
		src.nickname = null;

		byte[] bytes = MessagePack.pack(src);

		MyClassVersion1 dst = MessagePack.unpack(bytes, MyClassVersion1.class);

		assertEquals(dst.name, src.name);
		assertEquals(dst.nickname, src.nickname);
	}

	@Test
	public void testNullFields02() throws Exception {
		MyClassVersion1 src = new MyClassVersion1();
		src.name = null;
		src.nickname = "frsyuki";

		try {
			byte[] bytes = MessagePack.pack(src);
		} catch (Exception e) {
			assertTrue(true);
			return;
		}
		assertTrue(false);
	}

	@Test
	public void testNullFields03() throws Exception {
		List<String> src = new ArrayList<String>();
		src.add(null);
		src.add("frsyuki");

		byte[] bytes = MessagePack.pack(src);

		try {
			MyClassVersion1 dst = MessagePack.unpack(bytes, MyClassVersion1.class);
		} catch (Exception e) {
			assertTrue(true);
			return;
		}
		assertTrue(false);
	}

	@Test
	public void testNullFields04() throws Exception {
		MyClassVersion3 src = new MyClassVersion3();
		src.name = "Sadayuki Furuhashi";
		src.nickname = null;
		src.age = 23;
		src.school = null;

		byte[] bytes = MessagePack.pack(src);

		MyClassVersion3 dst = MessagePack.unpack(bytes, MyClassVersion3.class);

		assertEquals(dst.name, src.name);
		assertEquals(dst.nickname, src.nickname);
	}
}

