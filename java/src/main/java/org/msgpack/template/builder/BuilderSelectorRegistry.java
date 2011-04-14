//
// MessagePack for Java
//
// Copyright (C) 2009-2011 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
package org.msgpack.template.builder;

import java.lang.reflect.Type;
import java.util.LinkedList;
import java.util.List;

import org.msgpack.template.BeansFieldEntryReader;

/**
 * Registry for BuilderSelectors.
 * You can modify BuilderSelector chain throw this class.
 * 
 * @author takeshita
 *
 */
public class BuilderSelectorRegistry {

	private static BuilderSelectorRegistry instance = new BuilderSelectorRegistry();

	static{
		initForJava();
	}
	
	public static BuilderSelectorRegistry getInstance(){
		return instance;
	}
	
	TemplateBuilder forceBuilder;
	
    List<BuilderSelector> builderSelectors = new LinkedList<BuilderSelector>();

	private BuilderSelectorRegistry(){
	}

	/**
	 * initialize BuilderSelectors for basic java enviroment.
	 */
	private static void initForJava(){
		instance.append(new ArrayTemplateBuilderSelector());
		
		if(isSupportJavassist()){
			instance.append(
					new AnnotationTemplateBuilderSelector(
							new JavassistTemplateBuilder()));
			instance.forceBuilder = new JavassistTemplateBuilder();

			//Java beans
			instance.append(new BeansTemplateBuilderSelector(
					new JavassistTemplateBuilder(
							new BeansFieldEntryReader(),
							new BuildContextFactory() {
								@Override
								public BuildContextBase createBuildContext(JavassistTemplateBuilder builder) {
									return new BeansBuildContext(builder);
								}
							}
					)));
		}else{
			instance.append(
					new AnnotationTemplateBuilderSelector(
							new ReflectionTemplateBuilder()));
			instance.forceBuilder = new ReflectionTemplateBuilder();
			
			//Java beans
			instance.append(new BeansTemplateBuilderSelector(
					new BeansTemplateBuilder()));
		}
		
		instance.append(new OrdinalEnumTemplateBuilderSelector());
		instance.append(new EnumTemplateBuilderSelector());
	}
	public static boolean isSupportJavassist(){
		try {
			return System.getProperty("java.vm.name").equals("Dalvik");
		} catch (Exception e) {
			return true;
		}
	}
	
    /**
     * Check whether same name BuilderSelector is registered.
     * @param builderSelectorName
     * @return
     */
    public boolean contains(String builderSelectorName){
    	for(BuilderSelector bs : builderSelectors){
    		if(bs.getName().equals(builderSelectorName)){
    			return true;
    		}
    	}
    	return false;
    }
    /**
     * Append BuilderSelector to tail
     * @param builderSelector
     */
    public void append(BuilderSelector builderSelector){
    	
    	if(contains(builderSelector.getName())){
			throw new RuntimeException("Duplicate BuilderSelector name:" + builderSelector.getName());
    	}
    	this.builderSelectors.add(builderSelector);
    }
    /**
     * Insert BuiderSelector to head
     * @param builderSelector
     */
    public void prepend(BuilderSelector builderSelector){
    	if(contains(builderSelector.getName())){
			throw new RuntimeException("Duplicate BuilderSelector name:" + builderSelector.getName());
    	}
    	if(builderSelectors.size() > 0){
    		this.builderSelectors.add(0, builderSelector);
    	}else{
    		this.builderSelectors.add(builderSelector);
    	}
    }
    
    /**
     * Insert BuilderSelector
     * @param index
     * @param builderSelector
     */
    public void insert(int index,BuilderSelector builderSelector){
    	if(contains(builderSelector.getName())){
			throw new RuntimeException("Duplicate BuilderSelector name:" + builderSelector.getName());
    	}
    	if(builderSelectors.size() > 0){
    		this.builderSelectors.add(index, builderSelector);
    		
    	}else{
    		this.builderSelectors.add(builderSelector);
    	}
    }
    /**
     * Replace same name BuilderSelector
     * @param builderSelector
     */
    public void replace(BuilderSelector builderSelector){
    	String name = builderSelector.getName();
    	int index = getIndex(name);
    	builderSelectors.add(index, builderSelector);
    	builderSelectors.remove(index + 1);
    }
    
    /**
     * Insert the BuilderSelector before BuilderSelector named "builderSelectorName".
     * @param builderSelectorName
     * @param builderSelector
     */
    public void insertBefore(String builderSelectorName,BuilderSelector builderSelector){
    	int index = getIndex(builderSelectorName);
    	
    	builderSelectors.add(index,builderSelector);
    }
    /**
     * Insert the BuilderSelector after BuilderSelector named "builderSelectorName".
     * @param builderSelectorName
     * @param builderSelector
     */
    public void insertAfter(String builderSelectorName,BuilderSelector builderSelector){
    	int index = getIndex(builderSelectorName);
    	if(index + 1 == builderSelectors.size()){
    		builderSelectors.add(builderSelector);
    	}else{
    		builderSelectors.add(index + 1 , builderSelector);
    	}
    }
    private int getIndex(String builderSelectorName){
    	int index = 0;
    	for(BuilderSelector bs : builderSelectors){
    		if(bs.getName().equals(builderSelectorName)){
    			break;
    		}
    		index++;
    	}
    	if(index >= builderSelectors.size()){
    		throw new RuntimeException(
    				String.format("BuilderSelector named %s does not exist",builderSelectorName));
    	}
    	return index;
    }
    
    
    public TemplateBuilder select(Type target){
    	for(BuilderSelector selector : builderSelectors){
    		if(selector.matchType(target)){
    			return selector.getTemplateBuilder(target);
    		}
    	}
    	return null;
    }

	public TemplateBuilder getForceBuilder() {
		return forceBuilder;
	}


	public void setForceBuilder(TemplateBuilder forceBuilder) {
		this.forceBuilder = forceBuilder;
	}
	
	
	

}
