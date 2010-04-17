package org.msgpack;

import org.msgpack.*;
import java.io.*;
import java.util.*;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestPackUnpack {
    public Object unpackOne(ByteArrayOutputStream out) {
        ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
        Unpacker upk = new Unpacker(in);
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
        Packer pk = new Packer(out);
        pk.pack(val);
        Object obj = unpackOne(out);
        int val2 = -1;
        if (obj instanceof Byte)
            val2 = ((Byte)obj).intValue();
        else if (obj instanceof Integer)
            val2 = ((Integer)obj).intValue();
        else if (obj instanceof Short)
            val2 = ((Short)obj).intValue();
        else if (obj instanceof Long)
            val2 = ((Long)obj).intValue();
        else {
            System.out.println("obj = " + obj.getClass());
            assertTrue(false);
        }
        assertEquals(val, val2);
    }
};
