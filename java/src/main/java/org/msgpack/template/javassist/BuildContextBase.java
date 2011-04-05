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
package org.msgpack.template.javassist;

import java.io.IOException;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Type;
import java.lang.Thread;

import org.msgpack.*;
import org.msgpack.template.*;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;
import javassist.LoaderClassPath;
import javassist.NotFoundException;
import javassist.ClassClassPath;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public abstract class BuildContextBase<T extends IFieldEntry> {
	
	private static Logger LOG = LoggerFactory.getLogger(JavassistTemplateBuilder.class);

	
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
	
	
	public abstract Template buildTemplate(Class<?> targetClass, T[] entries, Template[] templates);


	protected Template build(final String className) {
		try {
			reset(className);
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

	protected void reset(String className) {
		tmplName = className + "_$$_Template" + director.nextSeqId();
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