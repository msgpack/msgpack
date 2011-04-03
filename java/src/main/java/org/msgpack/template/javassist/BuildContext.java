
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



public class BuildContext extends BuildContextBase<FieldEntry> {
	protected IFieldEntry[] entries;
	protected Class<?> origClass;
	protected String origName;
	protected Template[] templates;
	protected int minimumArrayLength;

	public BuildContext(JavassistTemplateBuilder director) {
		super(director);
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
			IFieldEntry e = entries[i];
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
			IFieldEntry e = entries[i];
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
			IFieldEntry e = entries[i];
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

			IFieldEntry e = entries[i];
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
			IFieldEntry e = entries[i];
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

			IFieldEntry e = entries[i];
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

}