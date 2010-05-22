package org.msgpack;

import org.msgpack.*;
import java.io.*;
import java.util.*;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestPackUnpack {
    protected Object unpackOne(ByteArrayOutputStream out) {
        return unpackOne(out, null);
    }
    protected Object unpackOne(ByteArrayOutputStream out, Schema schema) {
        ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
        Unpacker upk = new Unpacker(in);
        if (schema != null)
            upk = upk.useSchema(schema);
        Iterator<Object> it = upk.iterator();
        assertEquals(true, it.hasNext());
        Object obj = it.next();
        assertEquals(false, it.hasNext());
        return obj;
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
    public void testInt(int val) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).pack(val);
        Object obj = unpackOne(out);
        if (obj instanceof Byte)
            assertEquals(val, ((Byte)obj).intValue());
        else if (obj instanceof Integer)
            assertEquals(val, ((Integer)obj).intValue());
        else if (obj instanceof Short)
            assertEquals(val, ((Short)obj).intValue());
        else if (obj instanceof Long)
            assertEquals(val, ((Long)obj).intValue());
        else {
            System.out.println("Got unexpected class: " + obj.getClass());
            assertTrue(false);
        }
    }

    @Test
    public void testFloat() throws Exception {
        testFloat((float)0.0);
        testFloat((float)-0.0);
        testFloat((float)1.0);
        testFloat((float)-1.0);
        testFloat((float)Float.MAX_VALUE);
        testFloat((float)Float.MIN_VALUE);
        testFloat((float)Float.NaN);
        testFloat((float)Float.NEGATIVE_INFINITY);
        testFloat((float)Float.POSITIVE_INFINITY);
        Random rand = new Random();
        for (int i = 0; i < 1000; i++)
            testFloat(rand.nextFloat());
    }
    public void testFloat(float val) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).pack(val);
        Object obj = unpackOne(out);
        if (obj instanceof Float)
            assertEquals(val, ((Float)obj).floatValue(), 10e-10);
        else {
            System.out.println("Got unexpected class: " + obj.getClass());
            assertTrue(false);
        }
    }

    @Test
    public void testDouble() throws Exception {
        testDouble((double)0.0);
        testDouble((double)-0.0);
        testDouble((double)1.0);
        testDouble((double)-1.0);
        testDouble((double)Double.MAX_VALUE);
        testDouble((double)Double.MIN_VALUE);
        testDouble((double)Double.NaN);
        testDouble((double)Double.NEGATIVE_INFINITY);
        testDouble((double)Double.POSITIVE_INFINITY);
        Random rand = new Random();
        for (int i = 0; i < 1000; i++)
            testDouble(rand.nextDouble());
    }
    public void testDouble(double val) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).pack(val);
        Object obj = unpackOne(out);
        if (obj instanceof Double)
            assertEquals(val, ((Double)obj).doubleValue(), 10e-10);
        else {
            System.out.println("Got unexpected class: " + obj.getClass());
            assertTrue(false);
        }
    }

    @Test
    public void testNil() throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).packNil();
        Object obj = unpackOne(out);
        assertEquals(null, obj);
    }

    @Test
    public void testBoolean() throws Exception {
        testBoolean(false);
        testBoolean(true);
    }
    public void testBoolean(boolean val) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).pack(val);
        Object obj = unpackOne(out);
        if (obj instanceof Boolean)
            assertEquals(val, ((Boolean)obj).booleanValue());
        else {
            System.out.println("Got unexpected class: " + obj.getClass());
            assertTrue(false);
        }
    }

    @Test
    public void testString() throws Exception {
        testString("");
        testString("a");
        testString("ab");
        testString("abc");
        // small size string
        for (int i = 0; i < 100; i++) {
            StringBuilder sb = new StringBuilder();
            int len = (int)Math.random() % 31 + 1;
            for (int j = 0; j < len; j++)
                sb.append('a' + ((int)Math.random()) & 26);
            testString(sb.toString());
        }
        // medium size string
        for (int i = 0; i < 100; i++) {
            StringBuilder sb = new StringBuilder();
            int len = (int)Math.random() % 100 + (1 << 15);
            for (int j = 0; j < len; j++)
                sb.append('a' + ((int)Math.random()) & 26);
            testString(sb.toString());
        }
        // large size string
        for (int i = 0; i < 10; i++) {
            StringBuilder sb = new StringBuilder();
            int len = (int)Math.random() % 100 + (1 << 31);
            for (int j = 0; j < len; j++)
                sb.append('a' + ((int)Math.random()) & 26);
            testString(sb.toString());
        }
    }
    public void testString(String val) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).pack(val);
        Object obj = unpackOne(out);
        if (obj instanceof byte[])
            assertEquals(val, new String((byte[])obj));
        else {
            System.out.println("obj=" + obj);
            System.out.println("Got unexpected class: " + obj.getClass());
            assertTrue(false);
        }
    }

    @Test
    public void testArray() throws Exception {
        List<Integer> emptyList = new ArrayList<Integer>();
        testArray(emptyList, Schema.parse("(array int)"));

        for (int i = 0; i < 1000; i++) {
            Schema schema = Schema.parse("(array int)");
            List<Integer> l = new ArrayList<Integer>();
            int len = (int)Math.random() % 1000 + 1;
            for (int j = 0; j < len; j++)
                l.add(j);
            testArray(l, schema);
        }
        for (int i = 0; i < 1000; i++) {
            Schema schema = Schema.parse("(array string)");
            List<String> l = new ArrayList<String>();
            int len = (int)Math.random() % 1000 + 1;
            for (int j = 0; j < len; j++)
                l.add(Integer.toString(j));
            testArray(l, schema);
        }
    }
    public void testArray(List val, Schema schema) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).pack(val);
        Object obj = unpackOne(out, schema);
        if (obj instanceof List)
            assertTrue(val.equals(obj));
        else {
            System.out.println("obj=" + obj);
            System.out.println("Got unexpected class: " + obj.getClass());
            assertTrue(false);
        }
    }

    @Test
    public void testMap() throws Exception {
        Map<Integer, Integer> emptyMap = new HashMap<Integer, Integer>();
        testMap(emptyMap, Schema.parse("(map int int)"));

        for (int i = 0; i < 1000; i++) {
            Schema schema = Schema.parse("(map int int)");
            Map<Integer, Integer> m = new HashMap<Integer, Integer>();
            int len = (int)Math.random() % 1000 + 1;
            for (int j = 0; j < len; j++)
                m.put(j, j);
            testMap(m, schema);
        }
        for (int i = 0; i < 1000; i++) {
            Schema schema = Schema.parse("(map string int)");
            Map<String, Integer> m = new HashMap<String, Integer>();
            int len = (int)Math.random() % 1000 + 1;
            for (int j = 0; j < len; j++)
                m.put(Integer.toString(j), j);
            testMap(m, schema);
        }
    }
    public void testMap(Map val, Schema schema) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        new Packer(out).pack(val);
        Object obj = unpackOne(out, schema);
        if (obj instanceof Map)
            assertTrue(val.equals(obj));
        else {
            System.out.println("obj=" + obj);
            System.out.println("Got unexpected class: " + obj.getClass());
            assertTrue(false);
        }
    }
};
