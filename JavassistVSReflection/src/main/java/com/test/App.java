package com.test;

import java.util.Map;

/**
 * Hello world!
 *
 */
public class App 
{
    public static void main( String[] args )
    {
        Reflection r = new Reflection();
        {
        SampleClass c = new SampleClass();
        r.init(c);

        long start = System.currentTimeMillis();
        for(int i = 0;i < 1000000;i++){
            Map<String,Object> m = r.toMap(c);
            SampleClass ret = (SampleClass)r.toObj(SampleClass.class,m);
        }
        long delta = System.currentTimeMillis() - start;

        System.out.println("Reflection = " + delta + " msec");
        }


        {
        SampleClass c = new SampleClass();
        long start = System.currentTimeMillis();
        for(int i = 0;i < 1000000;i++){
            Map<String,Object> m = r.toMapByCode(c);
            SampleClass ret = r.toObjByCode(m);
        }
        long delta = System.currentTimeMillis() - start;

        System.out.println("By code = " + delta + " msec");
        }

        {
        SampleClass c = new SampleClass();

        long start = System.currentTimeMillis();
        for(int i = 0;i < 1000000;i++){
            Map<String,Object> m = r.toMap(c);
            SampleClass ret = (SampleClass)r.toObj(SampleClass.class,m);
        }
        long delta = System.currentTimeMillis() - start;

        System.out.println("Reflection = " + delta + " msec");
        }
    }
}
