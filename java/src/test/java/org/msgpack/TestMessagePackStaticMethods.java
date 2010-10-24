package org.msgpack;

import org.msgpack.*;
import org.msgpack.object.*;
import static org.msgpack.Templates.*;

import java.io.*;
import java.util.*;
import java.math.BigInteger;

import org.junit.Test;
import junit.framework.TestCase;

public class TestMessagePackStaticMethods extends TestCase {
	@Test
	public void testPackToByteArray() throws Exception {
		byte[] a = MessagePack.pack("msgpack");
		byte[] b = MessagePack.pack((Object)1);
		byte[] c = MessagePack.pack((Object)null);

		{
			MessagePackObject aobj = MessagePack.unpack(a);
			MessagePackObject bobj = MessagePack.unpack(b);
			MessagePackObject cobj = MessagePack.unpack(c);

			assertEquals(aobj, RawType.create("msgpack"));
			assertEquals(bobj, IntegerType.create(1));
			assertEquals(cobj, NilType.create());
		}
	}

	@Test
	public void testPackToStream() throws Exception {
		ByteArrayOutputStream aout = new ByteArrayOutputStream();
		MessagePack.pack(aout, "msgpack");
		ByteArrayOutputStream bout = new ByteArrayOutputStream();
		MessagePack.pack(bout, (Object)1);
		ByteArrayOutputStream cout = new ByteArrayOutputStream();
		MessagePack.pack(cout, (Object)null);

		{
			InputStream ain = new ByteArrayInputStream(aout.toByteArray());
			MessagePackObject aobj = MessagePack.unpack(ain);
			InputStream bin = new ByteArrayInputStream(bout.toByteArray());
			MessagePackObject bobj = MessagePack.unpack(bin);
			InputStream cin = new ByteArrayInputStream(cout.toByteArray());
			MessagePackObject cobj = MessagePack.unpack(cin);

			assertEquals(aobj, RawType.create("msgpack"));
			assertEquals(bobj, IntegerType.create(1));
			assertEquals(cobj, NilType.create());
		}
	}

	@Test
	public void testCheckedPackToByteArray() throws Exception {
		byte[] a = MessagePack.pack("msgpack", TString);
		byte[] b = MessagePack.pack((Object)1, TInteger);
		byte[] c = MessagePack.pack((Object)null, TAny);

		{
			Object aobj = MessagePack.unpack(a, TString);
			Object bobj = MessagePack.unpack(b, TInteger);
			Object cobj_any = MessagePack.unpack(c, TAny);
			Object cobj_obj = MessagePack.unpack(c, tOptional(TAny));
			assertEquals(aobj, "msgpack");
			assertEquals(bobj, 1);
			assertEquals(cobj_any, NilType.create());
			assertEquals(cobj_obj, null);
		}

		{
			String  aobj = MessagePack.unpack(a, String.class);
			Integer bobj = MessagePack.unpack(b, Integer.class);
			Object  cobj = MessagePack.unpack(c, Object.class);
			assertEquals(aobj, "msgpack");
			assertEquals(bobj, (Integer)1);
			assertEquals(cobj, null);
		}
	}

	@Test
	public void testCheckedPackToStream() throws Exception {
		ByteArrayOutputStream aout = new ByteArrayOutputStream();
		MessagePack.pack(aout, "msgpack");
		ByteArrayOutputStream bout = new ByteArrayOutputStream();
		MessagePack.pack(bout, (Object)1);
		ByteArrayOutputStream cout = new ByteArrayOutputStream();
		MessagePack.pack(cout, (Object)null);

		{
			InputStream ain = new ByteArrayInputStream(aout.toByteArray());
			Object aobj = MessagePack.unpack(ain, TString);
			InputStream bin = new ByteArrayInputStream(bout.toByteArray());
			Object bobj = MessagePack.unpack(bin, TInteger);
			InputStream cin_any = new ByteArrayInputStream(cout.toByteArray());
			Object cobj_any = MessagePack.unpack(cin_any, TAny);
			InputStream cin_obj = new ByteArrayInputStream(cout.toByteArray());
			Object cobj_obj = MessagePack.unpack(cin_obj, tOptional(TAny));

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, 1);
			assertEquals(cobj_any, NilType.create());
			assertEquals(cobj_obj, null);
		}

		{
			InputStream ain = new ByteArrayInputStream(aout.toByteArray());
			String  aobj = MessagePack.unpack(ain, String.class);
			InputStream bin = new ByteArrayInputStream(bout.toByteArray());
			Integer bobj = MessagePack.unpack(bin, Integer.class);
			InputStream cin = new ByteArrayInputStream(cout.toByteArray());
			Object  cobj = MessagePack.unpack(cin, Object.class);

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, (Integer)1);
			assertEquals(cobj, null);
		}
	}
}

