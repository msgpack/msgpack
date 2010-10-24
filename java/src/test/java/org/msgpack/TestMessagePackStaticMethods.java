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

public class TestMessagePackStaticMethods extends TestCase {
	public static class ProvidedClass {
		public boolean bool;
		public String str;
		public List<Integer> list;

		public boolean equals(Object obj) {
			if (obj == this) {
				return true;
			}
			if (!(obj instanceof ProvidedClass)) {
				return false;
			}
			ProvidedClass o = (ProvidedClass)obj;
			return bool == o.bool && str.equals(o.str) && list.equals(o.list);
		}

		public String toString() {
			return "ProvidedClass<bool:"+bool+" str:"+str+" list:"+list+">";
		}
	}

	@MessagePackMessage
	public static class UserDefinedClass {
		public boolean bool;
		public String str;
		public List<Integer> list;

		public boolean equals(Object obj) {
			if (obj == this) {
				return true;
			}
			if (!(obj instanceof UserDefinedClass)) {
				return false;
			}
			UserDefinedClass o = (UserDefinedClass)obj;
			return bool == o.bool && str.equals(o.str) && list.equals(o.list);
		}

		public String toString() {
			return "UserDefinedClass<bool:"+bool+" str:"+str+" list:"+list+">";
		}
	}

	static {
		// provided classes needs registration
		MessagePack.register(ProvidedClass.class);
		// annotated classes doesn't need registration
	}

	@Test
	public void testPackToByteArray() throws Exception {
		byte[] a = MessagePack.pack("msgpack");
		byte[] b = MessagePack.pack((Object)1);
		byte[] c = MessagePack.pack((Object)null);
		byte[] d = MessagePack.pack(createStringList());
		byte[] e = MessagePack.pack(createProvidedClass());
		byte[] f = MessagePack.pack(createUserDefinedClass_dynamic());

		{
			MessagePackObject aobj = MessagePack.unpack(a);
			MessagePackObject bobj = MessagePack.unpack(b);
			MessagePackObject cobj = MessagePack.unpack(c);
			MessagePackObject dobj = MessagePack.unpack(d);
			MessagePackObject eobj = MessagePack.unpack(e);
			MessagePackObject fobj = MessagePack.unpack(f);

			assertEquals(aobj, RawType.create("msgpack"));
			assertEquals(bobj, IntegerType.create(1));
			assertEquals(cobj, NilType.create());
			assertEquals(dobj, createStringList_dynamic());
			assertEquals(eobj, createProvidedClass_dynamic());
			assertEquals(fobj, createUserDefinedClass_dynamic());
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
		MessagePack.pack(eout, createProvidedClass());
		ByteArrayOutputStream fout = new ByteArrayOutputStream();
		MessagePack.pack(fout, createUserDefinedClass());

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
			InputStream fin = new ByteArrayInputStream(fout.toByteArray());
			MessagePackObject fobj = MessagePack.unpack(fin);

			assertEquals(aobj, RawType.create("msgpack"));
			assertEquals(bobj, IntegerType.create(1));
			assertEquals(cobj, NilType.create());
			assertEquals(dobj, createStringList_dynamic());
			assertEquals(eobj, createProvidedClass_dynamic());
			assertEquals(fobj, createUserDefinedClass_dynamic());
		}
	}

	@Test
	public void testCheckedPackToByteArray() throws Exception {
		byte[] a = MessagePack.pack("msgpack", TString);
		byte[] b = MessagePack.pack((Object)1, TInteger);
		byte[] c = MessagePack.pack((Object)null, TAny);
		byte[] d = MessagePack.pack(createStringList(), tList(TString));
		byte[] e = MessagePack.pack(createProvidedClass(), tClass(ProvidedClass.class));
		byte[] f = MessagePack.pack(createUserDefinedClass(), tClass(UserDefinedClass.class));

		{
			Object aobj = MessagePack.unpack(a, TString);
			Object bobj = MessagePack.unpack(b, TInteger);
			Object cobj_any = MessagePack.unpack(c, TAny);
			Object cobj_obj = MessagePack.unpack(c, tOptional(TAny));
			Object dobj = MessagePack.unpack(d, tList(TString));
			Object eobj = MessagePack.unpack(e, tClass(ProvidedClass.class));
			Object fobj = MessagePack.unpack(f, tClass(UserDefinedClass.class));

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, 1);
			assertEquals(cobj_any, NilType.create());
			assertEquals(cobj_obj, null);
			assertEquals(dobj, createStringList());
			assertEquals(eobj, createProvidedClass());
			assertEquals(fobj, createUserDefinedClass());
		}

		{
			String  aobj = MessagePack.unpack(a, String.class);
			Integer bobj = MessagePack.unpack(b, Integer.class);
			Object  cobj = MessagePack.unpack(c, Object.class);
			ProvidedClass eobj = MessagePack.unpack(e, ProvidedClass.class);
			UserDefinedClass fobj = MessagePack.unpack(f, UserDefinedClass.class);

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, (Integer)1);
			assertEquals(cobj, null);
			assertEquals(eobj, createProvidedClass());
			assertEquals(fobj, createUserDefinedClass());
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
		MessagePack.pack(eout, createProvidedClass());
		ByteArrayOutputStream fout = new ByteArrayOutputStream();
		MessagePack.pack(fout, createUserDefinedClass());

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
			Object eobj = MessagePack.unpack(ein, tClass(ProvidedClass.class));
			InputStream fin = new ByteArrayInputStream(fout.toByteArray());
			Object fobj = MessagePack.unpack(fin, tClass(UserDefinedClass.class));

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, 1);
			assertEquals(cobj_any, NilType.create());
			assertEquals(cobj_obj, null);
			assertEquals(dobj, createStringList());
			assertEquals(eobj, createProvidedClass());
			assertEquals(fobj, createUserDefinedClass());
		}

		{
			InputStream ain = new ByteArrayInputStream(aout.toByteArray());
			String  aobj = MessagePack.unpack(ain, String.class);
			InputStream bin = new ByteArrayInputStream(bout.toByteArray());
			Integer bobj = MessagePack.unpack(bin, Integer.class);
			InputStream cin = new ByteArrayInputStream(cout.toByteArray());
			Object  cobj = MessagePack.unpack(cin, Object.class);
			InputStream ein = new ByteArrayInputStream(eout.toByteArray());
			ProvidedClass eobj = MessagePack.unpack(ein, ProvidedClass.class);
			InputStream fin = new ByteArrayInputStream(fout.toByteArray());
			UserDefinedClass fobj = MessagePack.unpack(fin, UserDefinedClass.class);

			assertEquals(aobj, "msgpack");
			assertEquals(bobj, (Integer)1);
			assertEquals(cobj, null);
			assertEquals(eobj, createProvidedClass());
			assertEquals(fobj, createUserDefinedClass());
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


	private ProvidedClass createProvidedClass() {
		ProvidedClass obj = new ProvidedClass();
		obj.bool = true;
		obj.str = "viver";
		obj.list = new ArrayList<Integer>();
		obj.list.add(1);
		obj.list.add(2);
		obj.list.add(3);
		return obj;
	}

	private MessagePackObject createProvidedClass_dynamic() {
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


	private UserDefinedClass createUserDefinedClass() {
		UserDefinedClass obj = new UserDefinedClass();
		obj.bool = false;
		obj.str = "muga";
		obj.list = new ArrayList<Integer>();
		obj.list.add(9);
		obj.list.add(10);
		obj.list.add(11);
		return obj;
	}

	private MessagePackObject createUserDefinedClass_dynamic() {
		MessagePackObject[] obj = new MessagePackObject[3];
		obj[0] = BooleanType.create(false);
		obj[1] = RawType.create("muga");
		MessagePackObject[] list = new MessagePackObject[3];
		list[0] = IntegerType.create(9);
		list[1] = IntegerType.create(10);
		list[2] = IntegerType.create(11);
		obj[2] = ArrayType.create(list);
		return ArrayType.create(obj);
	}
}

