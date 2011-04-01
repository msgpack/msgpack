package org.msgpack.template;

import java.beans.BeanDescriptor;
import java.beans.BeanInfo;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyDescriptor;
import java.lang.annotation.Annotation;
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import org.msgpack.annotation.Ignore;
import org.msgpack.annotation.Index;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.Nullable;
import org.msgpack.annotation.Optional;
import org.msgpack.annotation.Required;

/**
 * List up Java beans property methods.
 * @author takeshita
 *
 */
public class BeansFieldEntryReader implements IFieldEntryReader{


	public IFieldEntry[] convertFieldEntries(Class<?> targetClass, FieldList flist) throws NoSuchFieldException {
		List<FieldList.Entry> src = flist.getList();
		FieldEntry[] result = new FieldEntry[src.size()];
		for(int i=0; i < src.size(); i++) {
			FieldList.Entry s = src.get(i);
			if(s.isAvailable()) {
				result[i] = new FieldEntry(targetClass.getDeclaredField(s.getName()), s.getOption());
			} else {
				result[i] = new FieldEntry();
			}
		}
		return result;
	}
	
	@Override
	public IFieldEntry[] readFieldEntries(Class<?> targetClass,
			FieldOption implicitOption) {
		BeanInfo desc;
		try {
			desc = Introspector.getBeanInfo(targetClass);
		} catch (IntrospectionException e1) {
			throw new TemplateBuildException("Class must be java beans class:" + targetClass.getName());
		}
		
		PropertyDescriptor[] props = desc.getPropertyDescriptors();
		ArrayList<PropertyDescriptor> list = new ArrayList<PropertyDescriptor>();
		for(int i = 0;i < props.length;i++){
			PropertyDescriptor pd = props[i];
			if(!isIgnoreProp(pd)){
				list.add(pd);
			}
		}
		props = new PropertyDescriptor[list.size()];
		list.toArray(props);
		
		BeansFieldEntry[] entries = new BeansFieldEntry[props.length];
		for(int i = 0;i < props.length;i++){
			PropertyDescriptor p = props[i];
			int index = readPropIndex(p);
			if(index >= 0){
				if(entries[index] != null){
					throw new TemplateBuildException("duplicated index: "+index);
				}
				if(index >= entries.length){
					throw new TemplateBuildException("invalid index: "+index);
				}
				entries[index] = new BeansFieldEntry(p);
				props[index] = null;
			}
		}
		int insertIndex = 0;
		for(int i = 0;i < props.length;i++){
			PropertyDescriptor p = props[i];
			if(p != null){
				while(entries[insertIndex] != null){
					insertIndex++;
				}
				entries[insertIndex] = new BeansFieldEntry(p);
			}
			
		}
	    for(int i = 0;i < entries.length;i++){
	    	BeansFieldEntry e = entries[i];
	    	FieldOption op = readPropOption(e.desc, implicitOption);
	    	e.setOption(op);
	    }
		return entries;
	}

	public FieldOption readImplicitFieldOption(Class<?> targetClass) {
		MessagePackMessage a = targetClass.getAnnotation(MessagePackMessage.class);
		if(a == null) {
			return FieldOption.DEFAULT;
		}
		return a.value();
	}
	

	private FieldOption readPropOption(PropertyDescriptor desc, FieldOption implicitOption) {
		
		FieldOption forGetter = readMethodOption(desc.getReadMethod());
		if(forGetter != FieldOption.DEFAULT){
			return forGetter;
		}
		FieldOption forSetter = readMethodOption(desc.getWriteMethod());
		if(forSetter != FieldOption.DEFAULT){
			return forSetter;
		}else{
			return implicitOption;
		}
		
	}
	private FieldOption readMethodOption(Method method){

		if(isAnnotated(method, Ignore.class)) {
			return FieldOption.IGNORE;
		} else if(isAnnotated(method, Required.class)) {
			return FieldOption.REQUIRED;
		} else if(isAnnotated(method, Optional.class)) {
			return FieldOption.OPTIONAL;
		} else if(isAnnotated(method, Nullable.class)) {
			if(method.getDeclaringClass().isPrimitive()) {
				return FieldOption.REQUIRED;
			} else {
				return FieldOption.NULLABLE;
			}
		}
		return FieldOption.DEFAULT;
	}

	private int readPropIndex(PropertyDescriptor desc) {
		
		int forGetter = readMethodIndex(desc.getReadMethod());
		if(forGetter >= 0){
			return forGetter;
		}
		int forSetter = readMethodIndex(desc.getWriteMethod());
		return forSetter;
	}
	private int readMethodIndex(Method method){
		Index a = method.getAnnotation(Index.class);
		if(a == null) {
			return -1;
		} else {
			return a.value();
		}
	}

	private boolean isAnnotated(AccessibleObject ao, Class<? extends Annotation> with) {
		return ao.getAnnotation(with) != null;
	}
	boolean isIgnoreProp(PropertyDescriptor desc){
		if(desc == null)return true;
		Method getter = desc.getReadMethod();
		Method setter = desc.getWriteMethod();
		return getter == null ||
		setter == null ||
		!Modifier.isPublic(getter.getModifiers()) ||
		!Modifier.isPublic(setter.getModifiers()) ||
		isAnnotated(getter,Ignore.class) ||
		isAnnotated(setter, Ignore.class);
	}
}
