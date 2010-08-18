package org.msgpack;

import org.msgpack.*;
import org.msgpack.object.*;
import java.math.BigInteger;
import java.util.*;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestObjectEquals {
	public void testInt(int val) throws Exception {
		MessagePackObject objInt = IntegerType.create(val);
		MessagePackObject objLong = IntegerType.create((long)val);
		MessagePackObject objBigInt = IntegerType.create(BigInteger.valueOf((long)val));
		assertTrue(objInt.equals(objInt));
		assertTrue(objInt.equals(objLong));
		assertTrue(objInt.equals(objBigInt));
		assertTrue(objLong.equals(objInt));
		assertTrue(objLong.equals(objLong));
		assertTrue(objLong.equals(objBigInt));
		assertTrue(objBigInt.equals(objInt));
		assertTrue(objBigInt.equals(objLong));
		assertTrue(objBigInt.equals(objBigInt));
	}
	@Test
	public void testInt() throws Exception {
		testInt(0);
		testInt(-1);
		testInt(1);
		testInt(Integer.MIN_VALUE);
		testInt(Integer.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++)
			testInt(rand.nextInt());
	}

	public void testLong(long val) throws Exception {
		MessagePackObject objInt = IntegerType.create((int)val);
		MessagePackObject objLong = IntegerType.create(val);
		MessagePackObject objBigInt = IntegerType.create(BigInteger.valueOf(val));
		if(val > (long)Integer.MAX_VALUE || val < (long)Integer.MIN_VALUE) {
			assertTrue(objInt.equals(objInt));
			assertFalse(objInt.equals(objLong));
			assertFalse(objInt.equals(objBigInt));
			assertFalse(objLong.equals(objInt));
			assertTrue(objLong.equals(objLong));
			assertTrue(objLong.equals(objBigInt));
			assertFalse(objBigInt.equals(objInt));
			assertTrue(objBigInt.equals(objLong));
			assertTrue(objBigInt.equals(objBigInt));
		} else {
			assertTrue(objInt.equals(objInt));
			assertTrue(objInt.equals(objLong));
			assertTrue(objInt.equals(objBigInt));
			assertTrue(objLong.equals(objInt));
			assertTrue(objLong.equals(objLong));
			assertTrue(objLong.equals(objBigInt));
			assertTrue(objBigInt.equals(objInt));
			assertTrue(objBigInt.equals(objLong));
			assertTrue(objBigInt.equals(objBigInt));
		}
	}
	@Test
	public void testLong() throws Exception {
		testLong(0);
		testLong(-1);
		testLong(1);
		testLong(Integer.MIN_VALUE);
		testLong(Integer.MAX_VALUE);
		testLong(Long.MIN_VALUE);
		testLong(Long.MAX_VALUE);
		Random rand = new Random();
		for (int i = 0; i < 1000; i++)
			testLong(rand.nextLong());
	}

	@Test
	public void testNil() throws Exception {
		assertTrue(NilType.create().equals(NilType.create()));
		assertFalse(NilType.create().equals(IntegerType.create(0)));
		assertFalse(NilType.create().equals(BooleanType.create(false)));
	}

	public void testString(String str) throws Exception {
		assertTrue(RawType.create(str).equals(RawType.create(str)));
	}
	@Test
	public void testString() throws Exception {
		testString("");
		testString("a");
		testString("ab");
		testString("abc");
	}
}

