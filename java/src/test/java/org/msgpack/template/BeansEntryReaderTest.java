package org.msgpack.template;

import java.beans.BeanDescriptor;
import java.beans.BeanInfo;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyDescriptor;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.msgpack.template.BeansFieldEntryReader;

import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.*;

/**
 * 
 * @author takeshita
 *
 */
public class BeansEntryReaderTest {
	
	public static class VariableProps{
		
		public int getCollect(){
			return 0;
		}
		public void setCollect(int v){}
		
		public int getOnlyGetter(){
			return 0;
		}
		
		public void setOnlySetter(int v){}
		
		public boolean isBoolean(){
			return true;
		}
		public void setBoolean(boolean b){}
		
		
		private int getPrivateBoth(){return 1;}
		private void setPrivateBoth(int v){}
		
		private int getPrivateGetter(){return 1;}
		public void setPrivateGetter(int v){}
		
		public int getPrivateSetter(){return 1;}
		private void setPrivateSetter(int v){}
		
		protected int getProtected(){return 1;}
		protected void setProtected(int v){}

		int getInternal(){return 1;}
		void setInternal(int v){}
		
		public int getWrongGetter(int v){return 1;}
		public void setWrongGetter(int v){}
		
		public void getWrongGetter2(){}
		public void setWrongGetter2(int v){}
		
		public int isWrongGetter3(){return 1;}
		public void setWrongGetter3(int v){}
		
		public int getWrongSetter(){return 1;}
		public int setWrongSetter(int v){return 1;}
		
		public int getWrongSetter2(){return 1;}
		public void setWrongSetter2(){}
	}
	
	@Before
	public void before(){
		reader = new BeansFieldEntryReader();
		
		try {
			info = Introspector.getBeanInfo(VariableProps.class);
		} catch (IntrospectionException e) {
			e.printStackTrace();
			Assert.fail();
		}
	}
	BeansFieldEntryReader reader;
	BeanInfo info;
	@Test
	public void testIgnorePropertyDesc(){
		BeanDescriptor desc = info.getBeanDescriptor();
		
		assertThat(reader.isIgnoreProp(getProp(info,"collect")),is(false));
		assertThat(reader.isIgnoreProp(getProp(info,"boolean")),is(false));
		

		assertThat(reader.isIgnoreProp(getProp(info,"onlyGetter")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"onlySetter")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"privateBoth")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"privateGetter")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"privateSetter")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"protected")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"internal")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"wrongGetter")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"wrongGetter2")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"wrongGetter3")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"wrongSetter")),is(true));
		assertThat(reader.isIgnoreProp(getProp(info,"wrongSetter2")),is(true));
		
	}
	@Test
	public void testReadEntries(){
		
		IFieldEntry[] entries = reader.readFieldEntries(VariableProps.class, FieldOption.DEFAULT);
		
		assertThat(entries.length, is(2));
		
		
	}
	
	
	public PropertyDescriptor getProp(BeanInfo info , String name){
		PropertyDescriptor[] props = info.getPropertyDescriptors();
		for(int i = 0;i < props.length;i++){
			PropertyDescriptor d = props[i];
			if(d.getDisplayName().equalsIgnoreCase(name)){
				return d;
			}
		}
		return null;
	}
	
	

}
