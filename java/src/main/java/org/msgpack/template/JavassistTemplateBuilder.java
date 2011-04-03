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
package org.msgpack.template;

import java.io.IOException;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Type;

import org.msgpack.*;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.LoaderClassPath;
import javassist.NotFoundException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class JavassistTemplateBuilder extends TemplateBuilder {
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

	private JavassistTemplateBuilder() {
		pool = new ClassPool();
		boolean appended = false;
		ClassLoader cl = null;
		try {
			Thread.currentThread().getContextClassLoader();
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

	protected ClassPool pool;

	private int seqId = 0;

	CtClass makeCtClass(String className) {
		return pool.makeClass(className);
	}

	CtClass getCtClass(String className) throws NotFoundException {
		return pool.get(className);
	}

	int nextSeqId() {
		return seqId++;
	}

	private static abstract class BuildContextBase {
		protected JavassistTemplateBuilder director;

		protected String tmplName;

		protected CtClass tmplCtClass;

		protected abstract void setSuperClass() throws CannotCompileException, NotFoundException;

		protected abstract void buildConstructor() throws CannotCompileException, NotFoundException;

		protected void buildMethodInit() { }

		protected abstract String buildPackMethodBody();

		protected abstract String buildUnpackMethodBody();

		protected abstract String buildConvertMethodBody();

		protected abstract Template buildInstance(Class<?> c) throws NoSuchMethodException, InstantiationException, IllegalAccessException, InvocationTargetException;

		public BuildContextBase(JavassistTemplateBuilder director) {
			this.director = director;
		}

		protected void write(final String className, final String directoryName) {
			try {
				reset(className, false);
				buildClass();
				buildConstructor();
				buildMethodInit();
				buildPackMethod();
				buildUnpackMethod();
				buildConvertMethod();
				writeClassFile(directoryName);
			} catch (Exception e) {
				String code = getBuiltString();
				if(code != null) {
					LOG.error("builder: " + code, e);
					throw new TemplateBuildException("cannot compile: " + code, e);
				} else {
					throw new TemplateBuildException(e);
				}
			}
		}
		protected void writeClassFile(final String directoryName) throws CannotCompileException, IOException {
			tmplCtClass.writeFile(directoryName);
		}

		protected Template build(final String className) {
			try {
				reset(className, true);
				buildClass();
				buildConstructor();
				buildMethodInit();
				buildPackMethod();
				buildUnpackMethod();
				buildConvertMethod();
				return buildInstance(createClass());
			} catch (Exception e) {
				String code = getBuiltString();
				if(code != null) {
					LOG.error("builder: " + code, e);
					throw new TemplateBuildException("cannot compile: " + code, e);
				} else {
					throw new TemplateBuildException(e);
				}
			}
		}

		protected void reset(String className, boolean isBuilt) {
			if (isBuilt) {
				tmplName = className + "_$$_Template" + director.nextSeqId();
			} else {
				tmplName = className + "_$$_Template";
			}
			tmplCtClass = director.makeCtClass(tmplName);
		}

		protected void buildClass() throws CannotCompileException, NotFoundException {
			setSuperClass();
			tmplCtClass.addInterface(director.getCtClass(Template.class.getName()));
		}

		protected void buildPackMethod() throws CannotCompileException, NotFoundException {
			String mbody = buildPackMethodBody();
			int mod = javassist.Modifier.PUBLIC;
			CtClass returnType = CtClass.voidType;
			String mname = "pack";
			CtClass[] paramTypes = new CtClass[] {
					director.getCtClass(Packer.class.getName()),
					director.getCtClass(Object.class.getName())
			};
			CtClass[] exceptTypes = new CtClass[] {
					director.getCtClass(IOException.class.getName())
			};
			CtMethod newCtMethod = CtNewMethod.make(
					mod, returnType, mname,
					paramTypes, exceptTypes, mbody, tmplCtClass);
			tmplCtClass.addMethod(newCtMethod);
		}

		protected void buildUnpackMethod() throws CannotCompileException, NotFoundException {
			String mbody = buildUnpackMethodBody();
			int mod = javassist.Modifier.PUBLIC;
			CtClass returnType = director.getCtClass(Object.class.getName());
			String mname = "unpack";
			CtClass[] paramTypes = new CtClass[] {
					director.getCtClass(Unpacker.class.getName()),
					director.getCtClass(Object.class.getName())
			};
			CtClass[] exceptTypes = new CtClass[] {
					director.getCtClass(MessageTypeException.class.getName())
			};
			CtMethod newCtMethod = CtNewMethod.make(
					mod, returnType, mname,
					paramTypes, exceptTypes, mbody, tmplCtClass);
			tmplCtClass.addMethod(newCtMethod);
		}

		protected void buildConvertMethod() throws CannotCompileException, NotFoundException {
			String mbody = buildConvertMethodBody();
			int mod = javassist.Modifier.PUBLIC;
			CtClass returnType = director.getCtClass(Object.class.getName());
			String mname = "convert";
			CtClass[] paramTypes = new CtClass[] {
					director.getCtClass(MessagePackObject.class.getName()),
					director.getCtClass(Object.class.getName())
			};
			CtClass[] exceptTypes = new CtClass[] {
					director.getCtClass(MessageTypeException.class.getName())
			};
			CtMethod newCtMethod = CtNewMethod.make(
					mod, returnType, mname,
					paramTypes, exceptTypes, mbody, tmplCtClass);
			tmplCtClass.addMethod(newCtMethod);
		}

		protected Class<?> createClass() throws CannotCompileException {
			return (Class<?>) tmplCtClass.toClass(null, null);
		}

		protected StringBuilder stringBuilder = null;

		protected void resetStringBuilder() {
			stringBuilder = new StringBuilder();
		}

		protected void buildString(String str) {
			stringBuilder.append(str);
		}

		protected void buildString(String format, Object... args) {
			stringBuilder.append(String.format(format, args));
		}

		protected String getBuiltString() {
			if(stringBuilder == null) {
				return null;
			}
			return stringBuilder.toString();
		}
	}

	public static abstract class JavassistTemplate extends AbstractTemplate {
		public Class<?> targetClass;
		public Template[] templates;

		public JavassistTemplate(Class<?> targetClass, Template[] templates) {
			this.targetClass = targetClass;
			this.templates = templates;
		}
	}

	private static class BuildContext extends BuildContextBase {
		protected FieldEntry[] entries;
		protected Class<?> origClass;
		protected String origName;
		protected Template[] templates;
		protected int minimumArrayLength;

		public BuildContext(JavassistTemplateBuilder director) {
			super(director);
		}

		public void writeTemplateClass(Class<?> targetClass, FieldEntry[] entries,
				Template[] templates, final String directoryName) {
			this.entries = entries;
			this.templates = templates;
			this.origClass = targetClass;
			this.origName = this.origClass.getName();
			write(this.origName, directoryName);
		}

		public Template buildTemplate(Class<?> targetClass, FieldEntry[] entries, Template[] templates) {
			this.entries = entries;
			this.templates = templates;
			this.origClass = targetClass;
			this.origName = this.origClass.getName();
			return build(this.origName);
		}

		protected void setSuperClass() throws CannotCompileException, NotFoundException {
			this.tmplCtClass.setSuperclass(
					director.getCtClass(JavassistTemplate.class.getName()));
		}

		protected void buildConstructor() throws CannotCompileException, NotFoundException {
			// Constructor(Class targetClass, Template[] templates)
			CtConstructor newCtCons = CtNewConstructor.make(
				new CtClass[] {
					director.getCtClass(Class.class.getName()),
					director.getCtClass(Template.class.getName()+"[]")
				},
				new CtClass[0],
				this.tmplCtClass);
			this.tmplCtClass.addConstructor(newCtCons);
		}

		protected Template buildInstance(Class<?> targetClass, Class<?> tmplClass, Template[] tmpls) {
			try {
				Constructor<?> cons = tmplClass.getConstructor(new Class[] {
						Class.class,
						Template[].class
				});
				Object tmpl = cons.newInstance(new Object[] {
						targetClass,
						tmpls
				});
				return (Template)tmpl;
			} catch (Exception e) {
				throw new TemplateBuildException(e);
			}
		}

		protected Template buildInstance(Class<?> c) throws NoSuchMethodException, InstantiationException, IllegalAccessException, InvocationTargetException {
			Constructor<?> cons = c.getConstructor(new Class[] {
					Class.class,
					Template[].class
				});
			Object tmpl = cons.newInstance(new Object[] {
					this.origClass,
					this.templates
				});
			return (Template)tmpl;
		}

		protected void buildMethodInit() {
			this.minimumArrayLength = 0;
			for(int i=0; i < entries.length; i++) {
				FieldEntry e = entries[i];
				if(e.isRequired() || e.isNullable()) {
					this.minimumArrayLength = i+1;
				}
			}
		}

		protected String buildPackMethodBody() {
			resetStringBuilder();
			buildString("{");
			buildString("%s _$$_t = (%s)$2;", this.origName, this.origName);
			buildString("$1.packArray(%d);", entries.length);
			for(int i=0; i < entries.length; i++) {
				FieldEntry e = entries[i];
				if(!e.isAvailable()) {
					buildString("$1.packNil();");
					continue;
				}
				Class<?> type = e.getType();
				if(type.isPrimitive()) {
					buildString("$1.%s(_$$_t.%s);", primitivePackName(type), e.getName());
				} else {
					buildString("if(_$$_t.%s == null) {", e.getName());
					if(!e.isNullable() && !e.isOptional()) {
						buildString("throw new %s();", MessageTypeException.class.getName());
					} else {
						buildString("$1.packNil();");
					}
					buildString("} else {");
					buildString("  this.templates[%d].pack($1, _$$_t.%s);", i, e.getName());
					buildString("}");
				}
			}
			buildString("}");
			return getBuiltString();
		}

		protected String buildUnpackMethodBody() {
			resetStringBuilder();
			buildString("{ ");

			buildString("%s _$$_t;", this.origName);
			buildString("if($2 == null) {");
			buildString("  _$$_t = new %s();", this.origName);
			buildString("} else {");
			buildString("  _$$_t = (%s)$2;", this.origName);
			buildString("}");

			buildString("int length = $1.unpackArray();");
			buildString("if(length < %d) {", this.minimumArrayLength);
			buildString("  throw new %s();", MessageTypeException.class.getName());
			buildString("}");

			int i;
			for(i=0; i < this.minimumArrayLength; i++) {
				FieldEntry e = entries[i];
				if(!e.isAvailable()) {
					buildString("$1.unpackObject();");
					continue;
				}

				buildString("if($1.tryUnpackNull()) {");
					if(e.isRequired()) {
						// Required + nil => exception
						buildString("throw new %s();", MessageTypeException.class.getName());
					} else if(e.isOptional()) {
						// Optional + nil => keep default value
					} else {  // Nullable
						// Nullable + nil => set null
						buildString("_$$_t.%s = null;", e.getName());
					}
				buildString("} else {");
					Class<?> type = e.getType();
					if(type.isPrimitive()) {
						buildString("_$$_t.%s = $1.%s();", e.getName(), primitiveUnpackName(type));
					} else {
						buildString("_$$_t.%s = (%s)this.templates[%d].unpack($1, _$$_t.%s);", e.getName(), e.getJavaTypeName(), i, e.getName());
					}
				buildString("}");
			}

			for(; i < entries.length; i++) {
				buildString("if(length <= %d) { return _$$_t; }", i);

				FieldEntry e = entries[i];
				if(!e.isAvailable()) {
					buildString("$1.unpackObject();");
					continue;
				}

				buildString("if($1.tryUnpackNull()) {");
					// this is Optional field becaue i >= minimumArrayLength
					// Optional + nil => keep default value
				buildString("} else {");
					Class<?> type = e.getType();
					if(type.isPrimitive()) {
						buildString("_$$_t.%s = $1.%s();", e.getName(), primitiveUnpackName(type));
					} else {
						buildString("_$$_t.%s = (%s)this.templates[%d].unpack($1, _$$_t.%s);", e.getName(), e.getJavaTypeName(), i, e.getName());
					}
				buildString("}");
			}

			// latter entries are all Optional + nil => keep default value

			buildString("for(int i=%d; i < length; i++) {", i);
			buildString("  $1.unpackObject();");
			buildString("}");

			buildString("return _$$_t;");

			buildString("}");
			return getBuiltString();
		}

		protected String buildConvertMethodBody() {
			resetStringBuilder();
			buildString("{ ");

			buildString("%s _$$_t;", this.origName);
			buildString("if($2 == null) {");
			buildString("  _$$_t = new %s();", this.origName);
			buildString("} else {");
			buildString("  _$$_t = (%s)$2;", this.origName);
			buildString("}");

			buildString("%s[] array = $1.asArray();", MessagePackObject.class.getName());
			buildString("int length = array.length;");
			buildString("if(length < %d) {", this.minimumArrayLength);
			buildString("  throw new %s();", MessageTypeException.class.getName());
			buildString("}");

			buildString("%s obj;", MessagePackObject.class.getName());

			int i;
			for(i=0; i < this.minimumArrayLength; i++) {
				FieldEntry e = entries[i];
				if(!e.isAvailable()) {
					continue;
				}

				buildString("obj = array[%d];", i);
				buildString("if(obj.isNil()) {");
					if(e.isRequired()) {
						// Required + nil => exception
						buildString("throw new %s();", MessageTypeException.class.getName());
					} else if(e.isOptional()) {
						// Optional + nil => keep default value
					} else {  // Nullable
						// Nullable + nil => set null
						buildString("_$$_t.%s = null;", e.getName());
					}
				buildString("} else {");
					Class<?> type = e.getType();
					if(type.isPrimitive()) {
						buildString("_$$_t.%s = obj.%s();", e.getName(), primitiveConvertName(type));
					} else {
						buildString("_$$_t.%s = (%s)this.templates[%d].convert(obj, _$$_t.%s);", e.getName(), e.getJavaTypeName(), i, e.getName());
					}
				buildString("}");
			}

			for(; i < entries.length; i++) {
				buildString("if(length <= %d) { return _$$_t; }", i);

				FieldEntry e = entries[i];
				if(!e.isAvailable()) {
					continue;
				}

				buildString("obj = array[%d];", i);
				buildString("if(obj.isNil()) {");
					// this is Optional field becaue i >= minimumArrayLength
					// Optional + nil => keep default value
				buildString("} else {");
					Class<?> type = e.getType();
					if(type.isPrimitive()) {
						buildString("_$$_t.%s = obj.%s();", e.getName(), primitiveConvertName(type));
					} else {
						buildString("_$$_t.%s = (%s)this.templates[%d].convert(obj, _$$_t.%s);", e.getName(), e.getJavaTypeName(), i, e.getName());
					}
				buildString("}");
			}

			// latter entries are all Optional + nil => keep default value

			buildString("return _$$_t;");

			buildString("}");
			return getBuiltString();
		}

		protected String primitivePackName(Class<?> type) {
			if(type == boolean.class) {
				return "packBoolean";
			} else if(type == byte.class) {
				return "packByte";
			} else if(type == short.class) {
				return "packShort";
			} else if(type == int.class) {
				return "packInt";
			} else if(type == long.class) {
				return "packLong";
			} else if(type == float.class) {
				return "packFloat";
			} else if(type == double.class) {
				return "packDouble";
			}
			return null;
		}

		protected String primitiveUnpackName(Class<?> type) {
			if(type == boolean.class) {
				return "unpackBoolean";
			} else if(type == byte.class) {
				return "unpackByte";
			} else if(type == short.class) {
				return "unpackShort";
			} else if(type == int.class) {
				return "unpackInt";
			} else if(type == long.class) {
				return "unpackLong";
			} else if(type == float.class) {
				return "unpackFloat";
			} else if(type == double.class) {
				return "unpackDouble";
			}
			return null;
		}

		protected String primitiveConvertName(Class<?> type) {
			if(type == boolean.class) {
				return "asBoolean";
			} else if(type == byte.class) {
				return "asByte";
			} else if(type == short.class) {
				return "asShort";
			} else if(type == int.class) {
				return "asInt";
			} else if(type == long.class) {
				return "asLong";
			} else if(type == float.class) {
				return "asFloat";
			} else if(type == double.class) {
				return "asDouble";
			}
			return null;
		}
	}

	@Override
	public Class<?> loadTemplateClass(Class<?> targetClass) {
		String tmplClassName = targetClass.getName() + "_$$_Template";
		ClassLoader cl = this.getClass().getClassLoader();// TODO
		try {
			return cl.loadClass(tmplClassName);
		} catch (ClassNotFoundException e) {
			LOG.debug("Tmplate class not found: " + tmplClassName);
			return null;
		}
	}

	@Override
	public Template initializeTemplate(Class<?> targetClass, Class<?> tmplClass, FieldEntry[] entries) {
		Template[] tmpls = toTemplates(entries);
		BuildContext bc = new BuildContext(this);
		return bc.buildInstance(targetClass, tmplClass, tmpls);
	}

	@Override
	public void writeTemplateClass(Class<?> targetClass, FieldEntry[] entries, String directoryName) {
		Template[] tmpls = toTemplates(entries);
		BuildContext bc = new BuildContext(this);
		bc.writeTemplateClass(targetClass, entries, tmpls, directoryName);
	}

	public Template buildTemplate(Class<?> targetClass, FieldEntry[] entries) {
		Template[] tmpls = toTemplates(entries);
		BuildContext bc = new BuildContext(this);
		return bc.buildTemplate(targetClass, entries, tmpls);
	}

	private static Template[] toTemplates(FieldEntry[] from) {
		// FIXME private / packagefields
		//for(FieldEntry e : entries) {
		//	Field f = e.getField();
		//	int mod = f.getModifiers();
		//	if(!Modifier.isPublic(mod)) {
		//		f.setAccessible(true);
		//	}
		//}

		Template[] tmpls = new Template[from.length];
		for(int i=0; i < from.length; i++) {
			FieldEntry e = from[i];
			if(!e.isAvailable()) {
				tmpls[i] = null;
			} else {
				Template tmpl = TemplateRegistry.lookup(e.getGenericType(), true);
				tmpls[i] = tmpl;
			}
		}
		return tmpls;
	}

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
	}
}

