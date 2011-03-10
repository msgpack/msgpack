
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

public abstract class JavassistTemplate extends AbstractTemplate {
	public Class<?> targetClass;
	public Template[] templates;

	public JavassistTemplate(Class<?> targetClass, Template[] templates) {
		this.targetClass = targetClass;
		this.templates = templates;
	}
}