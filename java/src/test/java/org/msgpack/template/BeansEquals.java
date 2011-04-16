package org.msgpack.template;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashSet;

import org.hamcrest.BaseMatcher;
import org.hamcrest.CoreMatchers;
import org.hamcrest.Description;
import org.junit.Assert;

/**
 * This matcher compares all get***() methods(except getClass)
 * @author takeshita
 *
 */
public class BeansEquals extends BaseMatcher<Object>{
	
	Object expected;
	
	HashSet<String> ignoreNames = new HashSet<String>();
	
	public BeansEquals(Object expected){
		this.expected = expected;
	}
	public BeansEquals(Object expected,String[] ignoreNames){
		this.expected = expected;
		for(int i = 0;i < ignoreNames.length;i++){
			this.ignoreNames.add(ignoreNames[i]);
		}
	}
	
	static String errorMessage = "hoge";

	@Override
	public boolean matches(Object actual) {
		if(expected == actual){
			return true;
		}
		if(!actual.getClass().equals(expected.getClass())){
			errorMessage = String.format("Expected class is %s but actual %s", 
					expected.getClass().getName(),
					actual.getClass().getName());
			return false;
		}
		
		for(Method m : expected.getClass().getMethods()){
			String n = m.getName();
			if(n.startsWith("get") &&
					!n.equals("getClass") &&
					!ignoreNames.contains(n)){
				
				if(m.getParameterTypes().length == 0 &&
						!m.getReturnType().equals(void.class)){
					try {
						Object exp = m.invoke(expected);
						Object act = m.invoke(actual);
						
						Assert.assertThat("@" + n,act, CoreMatchers.is(exp));
						
					} catch (Exception e) {
						throw new RuntimeException(String.format(
								"Exception occured while comparing %s",n), e);
					} 
					
				}
				
			}
			
		}

		return true;
	}

	
	@Override
	public void describeTo(Description desc) {
		
		desc.appendText(errorMessage);
	}
	

}
