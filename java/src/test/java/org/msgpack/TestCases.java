package org.msgpack;

import java.io.*;
import java.util.*;
import java.math.BigInteger;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestCases {
	public void feedFile(Unpacker pac, String path) throws Exception {
		FileInputStream input = new FileInputStream(path);
		byte[] buffer = new byte[32*1024];
		while(true) {
			int count = input.read(buffer);
			if(count < 0) {
				break;
			}
			pac.feed(buffer, 0, count);
		}
	}

	@Test
	public void testDynamicType() throws Exception {
		Unpacker pac = new Unpacker();
		Unpacker pac_compact = new Unpacker();

		feedFile(pac, "src/test/resources/cases.mpac");
		feedFile(pac_compact, "src/test/resources/cases_compact.mpac");

		UnpackResult result = new UnpackResult();
		UnpackResult result_compact = new UnpackResult();
		while(pac.next(result)) {
			assertTrue( pac_compact.next(result_compact) );
			assertTrue( result.getData().equals(result_compact.getData()) );
		}

		assertFalse( pac_compact.next(result) );
	}

	@Test
	public void testDirectConversion() throws Exception {
		Unpacker pac = new Unpacker();
		Unpacker pac_compact = new Unpacker();

		feedFile(pac, "src/test/resources/cases.mpac");
		feedFile(pac_compact, "src/test/resources/cases_compact.mpac");

		UnpackResult result_compact = new UnpackResult();
		while(pac_compact.next(result_compact)) {
			MessagePackObject obj = result_compact.getData();
			testDirectConversionRecursive(pac, obj);
		}

		assertFalse( pac_compact.next(result_compact) );
	}

	private void testDirectConversionRecursive(Unpacker pac, MessagePackObject obj) throws Exception {
		if(obj.isBooleanType()) {
			boolean expect = obj.asBoolean();
			boolean actual = pac.unpackBoolean();
			assertEquals(expect, actual);

		} else if(obj.isIntegerType()) {
			BigInteger expect = obj.asBigInteger();
			if(BigInteger.valueOf((long)Byte.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf((long)Byte.MAX_VALUE)) <= 0) {
				byte actual = pac.unpackByte();
				assertEquals(expect.byteValue(), actual);
			} else if(BigInteger.valueOf((long)Short.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf((long)Short.MAX_VALUE)) <= 0) {
				short actual = pac.unpackShort();
				assertEquals(expect.shortValue(), actual);
			} else if(BigInteger.valueOf((long)Integer.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf((long)Integer.MAX_VALUE)) <= 0) {
				int actual = pac.unpackInt();
				assertEquals(expect.intValue(), actual);
			} else if(BigInteger.valueOf(Long.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) <= 0) {
				long actual = pac.unpackLong();
				assertEquals(expect.longValue(), actual);
			} else {
				BigInteger actual = pac.unpackBigInteger();
				assertEquals(expect, actual);
			}

		} else if(obj.isFloatType()) {
			double expect = obj.asFloat();
			double actual = pac.unpackDouble();
			assertEquals(expect, actual, 0.01);

		} else if(obj.isArrayType()) {
			MessagePackObject[] expect = obj.asArray();
			int length = pac.unpackArray();
			assertEquals(expect.length, length);
			for(int i=0; i < length; i++) {
				testDirectConversionRecursive(pac, expect[i]);
			}

		} else if(obj.isMapType()) {
			Map<MessagePackObject, MessagePackObject> expect = obj.asMap();
			int size = pac.unpackMap();
			assertEquals(expect.size(), size);
			for(int i=0; i < size; i++) {
				MessagePackObject key = pac.unpackObject();
				MessagePackObject value = expect.get(key);
				assertNotNull(value);
				testDirectConversionRecursive(pac, value);
			}

		} else if(obj.isRawType()) {
			byte[] expect = obj.asByteArray();
			int length = pac.unpackRaw();
			assertEquals(expect.length, length);
			byte[] actual = pac.unpackRawBody(length);
			assertTrue(Arrays.equals(expect, actual));

		} else if(obj.isNil()) {
			pac.unpackNull();

		} else {
			fail("unexpected object: "+obj);
		}
	}

	@Test
	public void testIndirectConversion() throws Exception {
		Unpacker pac = new Unpacker();
		Unpacker pac_compact = new Unpacker();

		feedFile(pac, "src/test/resources/cases.mpac");
		feedFile(pac_compact, "src/test/resources/cases_compact.mpac");

		UnpackResult result = new UnpackResult();
		UnpackResult result_compact = new UnpackResult();
		while(pac.next(result)) {
			assertTrue( pac_compact.next(result_compact) );
			testIndirectConversionRecursive(result.getData(), result_compact.getData());
		}

		assertFalse( pac_compact.next(result) );
	}

	private void testIndirectConversionRecursive(MessagePackObject target, MessagePackObject obj) {
		if(obj.isBooleanType()) {
			boolean expect = obj.asBoolean();
			boolean actual = target.asBoolean();
			assertEquals(expect, actual);

		} else if(obj.isIntegerType()) {
			BigInteger expect = obj.asBigInteger();
			if(BigInteger.valueOf((long)Byte.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf((long)Byte.MAX_VALUE)) <= 0) {
				byte actual = target.asByte();
				assertEquals(expect.byteValue(), actual);
			} else if(BigInteger.valueOf((long)Short.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf((long)Short.MAX_VALUE)) <= 0) {
				short actual = target.asShort();
				assertEquals(expect.shortValue(), actual);
			} else if(BigInteger.valueOf((long)Integer.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf((long)Integer.MAX_VALUE)) <= 0) {
				int actual = target.asInt();
				assertEquals(expect.intValue(), actual);
			} else if(BigInteger.valueOf(Long.MIN_VALUE).compareTo(expect) <= 0 &&
					expect.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) <= 0) {
				long actual = target.asLong();
				assertEquals(expect.longValue(), actual);
			} else {
				BigInteger actual = target.asBigInteger();
				assertEquals(expect, actual);
			}

		} else if(obj.isFloatType()) {
			double expect = obj.asFloat();
			double actual = target.asDouble();
			assertEquals(expect, actual, 0.01);

		} else if(obj.isArrayType()) {
			MessagePackObject[] expect = obj.asArray();
			MessagePackObject[] actual = target.asArray();
			assertEquals(expect.length, actual.length);
			for(int i=0; i < expect.length; i++) {
				testIndirectConversionRecursive(actual[i], expect[i]);
			}

		} else if(obj.isMapType()) {
			Map<MessagePackObject, MessagePackObject> expect = obj.asMap();
			Map<MessagePackObject, MessagePackObject> actual = target.asMap();
			assertEquals(expect.size(), actual.size());
			for(Map.Entry<MessagePackObject,MessagePackObject> pair : expect.entrySet()) {
				MessagePackObject value = actual.get(pair.getKey());
				assertNotNull(value);
				testIndirectConversionRecursive(value, pair.getValue());
			}

		} else if(obj.isRawType()) {
			byte[] expect = obj.asByteArray();
			byte[] actual = obj.asByteArray();
			assertEquals(expect.length, actual.length);
			assertTrue(Arrays.equals(expect, actual));

		} else if(obj.isNil()) {
			assertTrue(target.isNil());

		} else {
			fail("unexpected object: "+obj);
		}
	}
};

