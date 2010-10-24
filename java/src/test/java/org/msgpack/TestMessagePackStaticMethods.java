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
	public static class CustomClass {
		public boolean bool;
		public String str;
		public List<Integer> list;

		public boolean equals(Object obj) {
			if (obj == this) {
				return true;
			}
			if (!(obj instanceof CustomClass)) {
				return false;
			}
			CustomClass o = (CustomClass)obj;
			return bool == o.bool && str.equals(o.str) && list.equals(o.list);
		}

		public String toString() {
			return "CustomClass<bool:"+bool+" str:"+str+" list:"+list+">";
		}
	}

	static {
		MessagePack.register(CustomClass.class);
	}

	@Test
	public void testPackToByteArray() throws Exception {
		byte[] a = MessagePack.pack("msgpack");
		byte[] b = MessagePack.pack((Object)1);
		byte[] c = MessagePack.pack((Object)null);
		byte[] d = MessagePack.pack(createStringList());
		byte[] e = MessagePack.pack(createCustomClass());

		{
			MessagePackObject aobj = MessagePack.unpack(a);
			MessagePackObject bobj = MessagePack.unpack(b);
			MessagePackObject cobj = MessagePack.unpack(c);
			MessagePackObject dobj = MessagePack.unpack(d);
			MessagePackObject eobj = MessagePack.unpack(e);

			assertEquals(aobj, RawType.create("msgpack"));
			assertEquals(bobj, IntegerType.create(1));
			assertEquals(cobj, NilType.create());
			assertEquals(dobj, createStringList_dynamic());
			assertEquals(eobj, createCustomClass_dynamic());
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
		ByteArrayOutputStream dout = new ByteArrayOutputStream();
		MessagePack.pack(dout, createStringList());
		ByteArrayOutputStream eout = new ByteArrayOutputStream();
		MessagePack.pack(eout, createCustomClass());

		{
			InputStream ain = new ByteArrayInputStream(aout.toByteArray());
			MessagePackObject aobj = MessagePack.unpack(ain);
			InputStream bin = new ByteArrayInputStream(bout.toByteArray());
			MessagePackObject bobj = MessagePack.unpack(bin);
			InputStream cin = new ByteArrayInputStream(cout.toByteArray());
			MessagePackObject cobj = MessagePack.unpack(cin);
			InputStream din = new ByteArrayInputStream(dout.toByteArray());
			MessagePackObject dobj = MessagePack.unpack(din);
			InputStream ein = new ByteArrayInputStream(eout.toByteArray());
			MessagePackObject eobj = MessagePack.unpack(ein);

			assertEquals(aobj, RawType.create("msgpack"));
			assertEquals(bobj, IntegerType.create(1));
			assertEquals(cobj, NilType.create());
			assertEquals(dobj, createStringList_dynamic());
			assertEquals(eobj, createCustomClass_dynamic());
		}
	}

	@Test
	public void testCheckedPackToByteArray() throws Exception {
		byte[] a = MessagePack.pack("msgpack", TString);
		byte[] b = MessagePack.pack((Object)1, TInteger);
		byte[] c = MessagePack.pack((Object)null, TAny);
		byte[] d = MessagePack.pack(createStringList(), tList(TString));
		byte[] e = MessagePack.pack(createCustomClass(), tClass(CustomClass.class));

		{
			Object aobj = MessagePack.unpack(a, TString);
			Object bobj = MessagePack.unpack(b, TInteger);
			Object cobj_any = MessagePack.unpack(c, TAny);
			Object cobj_obj = MessagePack.unpack(c, tOptional(TAny));
			Object dobj = MessagePack.unpack(d, tList(TString));
			Object eobj = MessagePack.unpack(e, tClass(CustomClass.class));

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, 1);
			assertEquals(cobj_any, NilType.create());
			assertEquals(cobj_obj, null);
			assertEquals(dobj, createStringList());
			assertEquals(eobj, createCustomClass());
		}

		{
			String  aobj = MessagePack.unpack(a, String.class);
			Integer bobj = MessagePack.unpack(b, Integer.class);
			Object  cobj = MessagePack.unpack(c, Object.class);
			CustomClass eobj = MessagePack.unpack(e, CustomClass.class);

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, (Integer)1);
			assertEquals(cobj, null);
			assertEquals(eobj, createCustomClass());
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
		ByteArrayOutputStream dout = new ByteArrayOutputStream();
		MessagePack.pack(dout, createStringList());
		ByteArrayOutputStream eout = new ByteArrayOutputStream();
		MessagePack.pack(eout, createCustomClass());

		{
			InputStream ain = new ByteArrayInputStream(aout.toByteArray());
			Object aobj = MessagePack.unpack(ain, TString);
			InputStream bin = new ByteArrayInputStream(bout.toByteArray());
			Object bobj = MessagePack.unpack(bin, TInteger);
			InputStream cin_any = new ByteArrayInputStream(cout.toByteArray());
			Object cobj_any = MessagePack.unpack(cin_any, TAny);
			InputStream cin_obj = new ByteArrayInputStream(cout.toByteArray());
			Object cobj_obj = MessagePack.unpack(cin_obj, tOptional(TAny));
			InputStream din = new ByteArrayInputStream(dout.toByteArray());
			Object dobj = MessagePack.unpack(din, tList(TString));
			InputStream ein = new ByteArrayInputStream(eout.toByteArray());
			Object eobj = MessagePack.unpack(ein, tClass(CustomClass.class));

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, 1);
			assertEquals(cobj_any, NilType.create());
			assertEquals(cobj_obj, null);
			assertEquals(dobj, createStringList());
			assertEquals(eobj, createCustomClass());
		}

		{
			InputStream ain = new ByteArrayInputStream(aout.toByteArray());
			String  aobj = MessagePack.unpack(ain, String.class);
			InputStream bin = new ByteArrayInputStream(bout.toByteArray());
			Integer bobj = MessagePack.unpack(bin, Integer.class);
			InputStream cin = new ByteArrayInputStream(cout.toByteArray());
			Object  cobj = MessagePack.unpack(cin, Object.class);
			InputStream ein = new ByteArrayInputStream(eout.toByteArray());
			Object  eobj = MessagePack.unpack(ein, CustomClass.class);

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, (Integer)1);
			assertEquals(cobj, null);
			assertEquals(eobj, createCustomClass());
		}
	}


	private List<String> createStringList() {
		List<String> list = new ArrayList<String>();
		list.add("frsyuki");
		list.add("kumofs");
		list.add("gem-compile");
		return list;
	}

	private MessagePackObject createStringList_dynamic() {
		MessagePackObject[] array = new MessagePackObject[3];
		array[0] = RawType.create("frsyuki");
		array[1] = RawType.create("kumofs");
		array[2] = RawType.create("gem-compile");
		return ArrayType.create(array);
	}


	private CustomClass createCustomClass() {
		CustomClass obj = new CustomClass();
		obj.bool = true;
		obj.str = "viver";
		obj.list = new ArrayList<Integer>();
		obj.list.add(1);
		obj.list.add(2);
		obj.list.add(3);
		return obj;
	}

	private MessagePackObject createCustomClass_dynamic() {
		MessagePackObject[] obj = new MessagePackObject[3];
		obj[0] = BooleanType.create(true);
		obj[1] = RawType.create("viver");
		MessagePackObject[] list = new MessagePackObject[3];
		list[0] = IntegerType.create(1);
		list[1] = IntegerType.create(2);
		list[2] = IntegerType.create(3);
		obj[2] = ArrayType.create(list);
		return ArrayType.create(obj);
	}
}

