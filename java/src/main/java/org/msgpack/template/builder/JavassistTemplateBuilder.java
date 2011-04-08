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

import java.lang.Thread;

import org.msgpack.*;

import javassist.ClassPool;
import javassist.CtClass;
import javassist.LoaderClassPath;
import javassist.NotFoundException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.msgpack.template.FieldEntryReader;
import org.msgpack.template.IFieldEntry;
import org.msgpack.template.IFieldEntryReader;
import org.msgpack.template.TemplateRegistry;

public class JavassistTemplateBuilder extends CustomTemplateBuilder {
	private static Logger LOG = LoggerFactory.getLogger(JavassistTemplateBuilder.class);

	private static JavassistTemplateBuilder instance;

	public synchronized static JavassistTemplateBuilder getInstance() {
		if(instance == null) {
			instance = new JavassistTemplateBuilder();
		}
		return instance;
	}

	public static void addClassLoader(ClassLoader cl) {
		getInstance().pool.appendClassPath(new LoaderClassPath(cl));
	}

	
	IFieldEntryReader reader = new FieldEntryReader();
	
	public void setFieldEntryReader(IFieldEntryReader reader){
		this.reader = reader;
	}
	
	BuildContextFactory buildContextFactory = new BuildContextFactory() {
		
		@Override
		public BuildContextBase createBuildContext(JavassistTemplateBuilder builder) {
			
			return new BuildContext(builder);
		}
	};
	public void setBuildContextFactory(BuildContextFactory factory){
		this.buildContextFactory = factory;
	}
	
	
	
	public JavassistTemplateBuilder() {
		pool = new ClassPool();
		boolean appended = false;
		ClassLoader cl = null;
		try {
			cl = Thread.currentThread().getContextClassLoader();
			if (cl != null) {
				pool.appendClassPath(new LoaderClassPath(cl));
				appended = true;
			}
		} catch (SecurityException e) {
			LOG.debug("Cannot append a search path of context classloader", e);
		}
		try {
			ClassLoader cl2 = getClass().getClassLoader();
			if (cl2 != null && cl2 != cl) {
				pool.appendClassPath(new LoaderClassPath(cl2));
				appended = true;
			}
		} catch (SecurityException e) {
			LOG.debug("Cannot append a search path of classloader", e);
		}
		if (!appended) {
			pool.appendSystemPath();
		}
	}
	/**
	 * Replace FieldEntryReader and BuilderContextFactory.
	 * you can replace field entry rules and generated codes easily.
	 * @param reader
	 * @param buildContextFactory
	 */
	public JavassistTemplateBuilder(IFieldEntryReader reader,BuildContextFactory buildContextFactory ){
		this();
		this.reader = reader;
		this.buildContextFactory = buildContextFactory;
	}


	protected ClassPool pool;

	private int seqId = 0;

	public CtClass makeCtClass(String className) {
		return pool.makeClass(className);
	}

	public CtClass getCtClass(String className) throws NotFoundException {
		return pool.get(className);
	}

	public int nextSeqId() {
		return seqId++;
	}


	@Override
	public Template buildTemplate(Class<?> targetClass, IFieldEntry[] entries) {
		// FIXME private / packagefields
		//for(FieldEntry e : entries) {
		//	Field f = e.getField();
		//	int mod = f.getModifiers();
		//	if(!Modifier.isPublic(mod)) {
		//		f.setAccessible(true);
		//	}
		//}

		Template[] tmpls = new Template[entries.length];
		for(int i=0; i < entries.length; i++) {
			IFieldEntry e = entries[i];
			if(!e.isAvailable()) {
				tmpls[i] = null;
			} else {
				Template tmpl = TemplateRegistry.lookup(e.getGenericType(), true);
				tmpls[i] = tmpl;
			}
		}

		BuildContextBase bc = getBuildContextFacotry().createBuildContext(this);
		return bc.buildTemplate(targetClass, entries, tmpls);
	}

	@Override
	public IFieldEntryReader getFieldEntryReader() {
		return reader;
	}

	public BuildContextFactory getBuildContextFacotry() {
		return buildContextFactory;
	}

	
    /*
	static class JavassistOrdinalEnumTemplate extends ReflectionTemplateBuilder.ReflectionOrdinalEnumTemplate {
		JavassistOrdinalEnumTemplate(Enum<?>[] entries) {
			super(entries);
		}
	}

	@Override
	public void writeOrdinalEnumTemplateClass(Class<?> targetClass, Enum<?>[] entires, String directoryName) {
		throw new UnsupportedOperationException("not supported yet.");// TODO
	}

	public Template buildOrdinalEnumTemplate(Class<?> targetClass, Enum<?>[] entries) {
		return new JavassistOrdinalEnumTemplate(entries);
	}

	@Override
	public void writeArrayTemplateClass(Type arrayType, Type genericBaseType,
			Class<?> baseClass, int dim, String directoryName) {
		throw new UnsupportedOperationException("not supported yet.");//TODO
	}

	public Template buildArrayTemplate(Type arrayType, Type genericBaseType, Class<?> baseClass, int dim) {
		if(dim == 1) {
			if(baseClass == boolean.class) {
				return BooleanArrayTemplate.getInstance();
			} else if(baseClass == short.class) {
				return ShortArrayTemplate.getInstance();
			} else if(baseClass == int.class) {
				return IntArrayTemplate.getInstance();
			} else if(baseClass == long.class) {
				return LongArrayTemplate.getInstance();
			} else if(baseClass == float.class) {
				return FloatArrayTemplate.getInstance();
			} else if(baseClass == double.class) {
				return DoubleArrayTemplate.getInstance();
			} else {
				// FIXME
				Template baseTemplate = TemplateRegistry.lookup(genericBaseType);
				return new ReflectionTemplateBuilder.ReflectionObjectArrayTemplate(baseClass, baseTemplate);
			}
		} else if(dim == 2) {
			// FIXME
			Class<?> componentClass = Array.newInstance(baseClass, 0).getClass();
			Template componentTemplate = buildArrayTemplate(arrayType, genericBaseType, baseClass, dim-1);
			return new ReflectionTemplateBuilder.ReflectionMultidimentionalArrayTemplate(componentClass, componentTemplate);
		} else {
			// FIXME
			ReflectionTemplateBuilder.ReflectionMultidimentionalArrayTemplate componentTemplate = (ReflectionTemplateBuilder.ReflectionMultidimentionalArrayTemplate)
				buildArrayTemplate(arrayType, genericBaseType, baseClass, dim-1);
			Class<?> componentClass = Array.newInstance(componentTemplate.getComponentClass(), 0).getClass();
			return new ReflectionTemplateBuilder.ReflectionMultidimentionalArrayTemplate(componentClass, componentTemplate);
		}
	}*/
}

