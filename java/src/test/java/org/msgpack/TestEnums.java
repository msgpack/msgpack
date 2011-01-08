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

public class TestEnums extends TestCase {
	public static enum ProvidedEnum {
		RED,
		GREEN,
		BLUE
	}

	@MessagePackOrdinalEnum
	public static enum UserDefinedEnum {
		CYAN,
		MAGENTA,
		YELLOW
	}

	@MessagePackOrdinalEnum
	public static enum UserDefinedEnumVersion2 {
		CYAN,
		MAGENTA,
		YELLOW,
		KEY
	}


	{
		// provided classes need registration
		MessagePack.register(ProvidedEnum.class);
		// annotated classes don't need registration
	}

	@Test
	public void testRegisteredEnum() {
		byte[] rout = MessagePack.pack(ProvidedEnum.RED);
		byte[] gout = MessagePack.pack(ProvidedEnum.GREEN);
		byte[] bout = MessagePack.pack(ProvidedEnum.BLUE);

		ProvidedEnum r = MessagePack.unpack(rout, ProvidedEnum.class);
		ProvidedEnum g = MessagePack.unpack(gout, ProvidedEnum.class);
		ProvidedEnum b = MessagePack.unpack(bout, ProvidedEnum.class);

		assertEquals(r, ProvidedEnum.RED);
		assertEquals(g, ProvidedEnum.GREEN);
		assertEquals(b, ProvidedEnum.BLUE);
	}

	@Test
	public void testAnnotatedEnum() {
		byte[] cout = MessagePack.pack(UserDefinedEnum.CYAN);
		byte[] mout = MessagePack.pack(UserDefinedEnum.MAGENTA);
		byte[] yout = MessagePack.pack(UserDefinedEnum.YELLOW);

		UserDefinedEnum c = MessagePack.unpack(cout, UserDefinedEnum.class);
		UserDefinedEnum m = MessagePack.unpack(mout, UserDefinedEnum.class);
		UserDefinedEnum y = MessagePack.unpack(yout, UserDefinedEnum.class);

		assertEquals(c, UserDefinedEnum.CYAN);
		assertEquals(m, UserDefinedEnum.MAGENTA);
		assertEquals(y, UserDefinedEnum.YELLOW);
	}

	@Test
	public void testBackwardCompatibility() {
		byte[] cout = MessagePack.pack(UserDefinedEnum.CYAN);
		byte[] mout = MessagePack.pack(UserDefinedEnum.MAGENTA);
		byte[] yout = MessagePack.pack(UserDefinedEnum.YELLOW);

		UserDefinedEnumVersion2 c = MessagePack.unpack(cout, UserDefinedEnumVersion2.class);
		UserDefinedEnumVersion2 m = MessagePack.unpack(mout, UserDefinedEnumVersion2.class);
		UserDefinedEnumVersion2 y = MessagePack.unpack(yout, UserDefinedEnumVersion2.class);

		assertEquals(c, UserDefinedEnumVersion2.CYAN);
		assertEquals(m, UserDefinedEnumVersion2.MAGENTA);
		assertEquals(y, UserDefinedEnumVersion2.YELLOW);
	}

	@Test
	public void testForwardCompatibility() {
		byte[] cout = MessagePack.pack(UserDefinedEnumVersion2.CYAN);
		byte[] mout = MessagePack.pack(UserDefinedEnumVersion2.MAGENTA);
		byte[] yout = MessagePack.pack(UserDefinedEnumVersion2.YELLOW);
		byte[] kout = MessagePack.pack(UserDefinedEnumVersion2.KEY);

		UserDefinedEnum c = MessagePack.unpack(cout, UserDefinedEnum.class);
		UserDefinedEnum m = MessagePack.unpack(mout, UserDefinedEnum.class);
		UserDefinedEnum y = MessagePack.unpack(yout, UserDefinedEnum.class);

		assertEquals(c, UserDefinedEnum.CYAN);
		assertEquals(m, UserDefinedEnum.MAGENTA);
		assertEquals(y, UserDefinedEnum.YELLOW);

		try {
			MessagePack.unpack(kout, UserDefinedEnum.class);
		} catch (Exception e) {
			assertTrue(true);
			return;
		}
		assertTrue(false);
	}
}

