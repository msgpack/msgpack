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
import java.lang.reflect.Type;

import org.msgpack.*;

import javassist.ClassPool;
import javassist.CtClass;
import javassist.LoaderClassPath;
import javassist.NotFoundException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.msgpack.template.FieldEntryReader;
import org.msgpack.template.FieldOption;
import org.msgpack.template.IFieldEntry;
import org.msgpack.template.IFieldEntryReader;
import org.msgpack.template.TemplateRegistry;

public class JavassistTemplateBuilder extends CustomTemplateBuilder {
	public static abstract class JavassistTemplate extends AbstractTemplate {
		public Class<?> targetClass;
		public Template[] templates;

		public JavassistTemplate(Class<?> targetClass, Template[] templates) {
			this.targetClass = targetClass;
			this.templates = templates;
		}
	}

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
		Template[] tmpls = toTemplate(entries);
		BuildContextBase bc = getBuildContextFacotry().createBuildContext(this);
		return bc.buildTemplate(targetClass, entries, tmpls);
	}

	private static Template[] toTemplate(IFieldEntry[] from) {
		Template[] tmpls = new Template[from.length];
		for(int i=0; i < from.length; i++) {
			IFieldEntry e = from[i];
			if(!e.isAvailable()) {
				tmpls[i] = null;
			} else {
				Template tmpl = TemplateRegistry.lookup(e.getGenericType(), true);
				tmpls[i] = tmpl;
			}
		}
		return tmpls;
	}

	@Override
	public IFieldEntryReader getFieldEntryReader() {
		return reader;
	}

	public BuildContextFactory getBuildContextFacotry() {
		return buildContextFactory;
	}

	@Override
	public void writeTemplate(Type targetType, String directoryName) {
		Class<?> targetClass = (Class<?>)targetType;
		IFieldEntryReader reader = getFieldEntryReader();
		FieldOption implicitOption = reader.readImplicitFieldOption(targetClass);
		checkValidation(targetClass);
		IFieldEntry[] entries = reader.readFieldEntries(targetClass, implicitOption);
		writeTemplate(targetClass, entries, directoryName);
	}

	private void writeTemplate(Class<?> targetClass, IFieldEntry[] entries, String directoryName) {
		Template[] tmpls = toTemplate(entries);
		BuildContextBase bc = getBuildContextFacotry().createBuildContext(this);
		bc.writeTemplate(targetClass, entries, tmpls, directoryName);
	}

	@Override
	public Template loadTemplate(Type targetType) {
		Class<?> targetClass = (Class<?>)targetType;
		IFieldEntryReader reader = getFieldEntryReader();
		FieldOption implicitOption = reader.readImplicitFieldOption(targetClass);
		checkValidation(targetClass);
		IFieldEntry[] entries = reader.readFieldEntries(targetClass, implicitOption);
		return loadTemplate(targetClass, entries);
	}

	private Template loadTemplate(Class<?> targetClass, IFieldEntry[] entries) {
		Template[] tmpls = toTemplate(entries);
		BuildContextBase bc = getBuildContextFacotry().createBuildContext(this);
		return bc.loadTemplate(targetClass, entries, tmpls);
	}
}

