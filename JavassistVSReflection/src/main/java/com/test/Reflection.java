package com.test;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

/**
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/11
 * Time: 0:16
 * To change this template use File | Settings | File Templates.
 */
public class Reflection {

    static class NameAndMethod{
        public String name;
        public Method method;

        public NameAndMethod(){}
        public NameAndMethod(String name , Method method){
            this.name = name;
            this.method = method;
        }

    }

    NameAndMethod[] array = null;

    Map<String,Method> setters = new HashMap<String,Method>();

    boolean init = false;

    void init(Object obj){

        if(!init){
            List<NameAndMethod> getters = new ArrayList<NameAndMethod>();
            Class<?> clazz = obj.getClass();
            for(Method m : clazz.getMethods()){
                if(m.getName().startsWith("get")){
                    getters.add(new NameAndMethod(m.getName().substring(3), m));
                }else if(m.getName().startsWith("set")){
                    setters.put(m.getName().substring(3),m);
                }
            }
            array = getters.toArray(new NameAndMethod[0]);

            init = true;
        }
    }

    public Map<String,Object> toMap(Object obj){
        Map<String,Object> result = new HashMap<String,Object>();

        for(int i = 0;i < array.length;i++){
            NameAndMethod nam = array[i];
            Method m = nam.method;
            try {
                result.put(nam.name,m.invoke(obj));
            } catch (IllegalAccessException e) {
                e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
            } catch (InvocationTargetException e) {
                e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
            }

        }



        return result;

    }

    public Object toObj(Class<?> clazz ,Map<String,Object> map){
         Object value = null;
        try {
            value = clazz.getConstructor().newInstance();
        } catch (InstantiationException e) {
            e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
        } catch (IllegalAccessException e) {
            e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
        } catch (InvocationTargetException e) {
            e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
        } catch (NoSuchMethodException e) {
            e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
        }
        for(Map.Entry<String,Method> setter : setters.entrySet()){
            Method m = setter.getValue();
            try {
                m.invoke(value,map.get(setter.getKey()));
            } catch (IllegalAccessException e) {
                e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
            } catch (InvocationTargetException e) {
                e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
            }
        }

        return value;
    }



    public Map<String,Object> toMapByCode(SampleClass obj){

        Map<String,Object> map = new HashMap<String,Object>();

        map.put("name",obj.getName());
        map.put("address",obj.getAddress());
        map.put("a",obj.getA());
        map.put("b",obj.getB());
        map.put("phoneNumber",obj.getPhoneNumber());
        map.put("gender",obj.getGender());
        map.put("id",obj.getId());

        return map;
    }

    public SampleClass toObjByCode(Map<String,Object> map){
        SampleClass sc = new SampleClass();
        sc.setA((String)map.get("b"));
        sc.setB((String) map.get("b"));
        sc.setAddress((String)map.get("address"));
        sc.setName((String)map.get("name"));
        sc.setPhoneNumber((String)map.get("phoneNumber"));
        sc.setGender((String)map.get("gender"));
        sc.setId((Integer)map.get("id"));

        return sc;
    }



}
