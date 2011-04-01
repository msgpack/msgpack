//
// MessagePack for Java
//
// Copyright (C) 2009-2010 FURUHASHI Sadayuki
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

import java.util.Map;
import java.util.HashMap;
import java.lang.reflect.Type;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.annotation.Annotation;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackDelegate;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.msgpack.template.builder.BuilderSelectorRegistry;
import org.msgpack.template.builder.CustomTemplateBuilder;
import org.msgpack.template.builder.TemplateBuilder;
import org.msgpack.Template;
import org.msgpack.Templates;

public class TemplateRegistry {
	private static Map<Type, Template> map;
	private static Map<Type, GenericTemplate> genericMap;
	
	private static BuilderSelectorRegistry builderSelectorRegistry;

	static {
		map = new HashMap<Type, Template>();
		genericMap = new HashMap<Type, GenericTemplate>();
		BuiltInTemplateLoader.load();
		builderSelectorRegistry = BuilderSelectorRegistry.getInstance();
	}

	public static void register(Class<?> target) { // auto-detect
		TemplateBuilder builder = builderSelectorRegistry.select(target);
		if(builder != null){
			register(target,builder.buildTemplate(target));
		}else{
			register(target,builderSelectorRegistry.getForceBuilder().buildTemplate(target));
		}
		/*if(target.isEnum()) {
			register(target, TemplateBuilder.buildOrdinalEnum(target));
		} else {
			register(target, TemplateBuilder.build(target));
		}*/
	}

	public static void register(Class<?> target, FieldOption implicitOption) {
		TemplateBuilder builder = builderSelectorRegistry.select(target);
		if(builder != null && builder instanceof CustomTemplateBuilder){
			register(target, ((CustomTemplateBuilder)builder).buildTemplate(target, implicitOption));
		}else{
			throw new TemplateBuildException("cannot build template with filed option");
		}
	}

	public static void register(Class<?> target, FieldList flist) throws NoSuchFieldException {
		TemplateBuilder builder = builderSelectorRegistry.select(target);
		if(builder != null && builder instanceof CustomTemplateBuilder){
			register(target, ((CustomTemplateBuilder)builder).buildTemplate(target, flist));
		}else{
			throw new TemplateBuildException("cannot build template with filed list");
		}
	}

	public static synchronized void register(Type rawType, Template tmpl) {
		if(rawType instanceof ParameterizedType) {
			rawType = ((ParameterizedType)rawType).getRawType();
		}
		map.put(rawType, tmpl);
	}

	public static synchronized void registerGeneric(Type rawType, GenericTemplate gtmpl) {
		if(rawType instanceof ParameterizedType) {
			rawType = ((ParameterizedType)rawType).getRawType();
		}
		genericMap.put(rawType, gtmpl);
	}

	public static synchronized Template lookup(Type targetType) {
		return lookupImpl(targetType, false, true);
	}

	public static synchronized Template lookup(Type targetType, boolean forceBuild) {
		return lookupImpl(targetType, forceBuild, true);
	}

	public static synchronized Template tryLookup(Type targetType) {
		return lookupImpl(targetType, false, false);
	}

	public static synchronized Template tryLookup(Type targetType, boolean forceBuild) {
		return lookupImpl(targetType, forceBuild, false);
	}

	private static synchronized Template lookupImpl(Type targetType, boolean forceBuild, boolean fallbackDefault) {
		Template tmpl;

		if(targetType instanceof ParameterizedType) {
			// ParameterizedType is not a Class<?>?
			tmpl = lookupGenericImpl((ParameterizedType)targetType);
			if(tmpl != null) {
				return tmpl;
			}
			targetType = ((ParameterizedType)targetType).getRawType();
		}

		tmpl = map.get(targetType);
		if(tmpl != null) {
			return tmpl;
		}

		/*if(targetType instanceof GenericArrayType) {
			// GenericArrayType is not a Class<?>
			tmpl = TemplateBuilder.buildArray(targetType);
			register(targetType, tmpl);
			return tmpl;
		}

		Class<?> target = (Class<?>)targetType;

		if(target.isArray()) {
			// FIXME can't distinguish type-erased T<>[]?
			tmpl = TemplateBuilder.buildArray(target);
			register(target, tmpl);
			return tmpl;
		}

		if(isAnnotated(target, MessagePackMessage.class)) {
			tmpl = TemplateBuilder.build(target);
			register(target, tmpl);
			return tmpl;
		} else if(isAnnotated(target, MessagePackDelegate.class)) {
			// TODO DelegateTemplate
			throw new UnsupportedOperationException("not supported yet. : " + target.getName());
		} else if(isAnnotated(target, MessagePackOrdinalEnum.class)) {
			tmpl = TemplateBuilder.buildOrdinalEnum(target);
			register(target, tmpl);
			return tmpl;
		}*/
		// find match TemplateBuilder
		TemplateBuilder builder = BuilderSelectorRegistry.getInstance().select(targetType);
		if(builder != null){
			tmpl = builder.buildTemplate(targetType);
			register(targetType,tmpl);
			return tmpl;
		}
		
		
		Class<?> target = (Class<?>)targetType;

		for(Class<?> i : target.getInterfaces()) {
			tmpl = map.get(i);
			if(tmpl != null) {
				register(target, tmpl);
				return tmpl;
			}
		}

		Class<?> c = target.getSuperclass();
		if(c != null) {
			for(; c != Object.class; c = c.getSuperclass()) {
				tmpl = map.get(c);
				if(tmpl != null) {
					register(target, tmpl);
					return tmpl;
				}
			}

			if(forceBuild) {
				tmpl = builderSelectorRegistry.getForceBuilder().buildTemplate(target);
				register(target, tmpl);
				return tmpl;
			}
		}

		if(fallbackDefault) {
			tmpl = new DefaultTemplate((Class<?>)target);
			register(target, tmpl);
			return tmpl;
		} else {
			return null;
		}
	}

	public static synchronized Template lookupGeneric(Type targetType) {
		if(targetType instanceof ParameterizedType) {
			ParameterizedType parameterizedType = (ParameterizedType)targetType;
			Template tmpl = lookupGenericImpl(parameterizedType);
			if(tmpl != null) {
				return tmpl;
			}
			return new DefaultTemplate((Class<?>)parameterizedType.getRawType(), parameterizedType);
		} else {
			throw new IllegalArgumentException("actual types of the generic type are erased: "+targetType);
		}
	}

	private static synchronized Template lookupGenericImpl(ParameterizedType type) {
		Type rawType = type.getRawType();
		GenericTemplate gtmpl = genericMap.get(rawType);
		if(gtmpl == null) {
			return null;
		}

		Type[] types = type.getActualTypeArguments();
		Template[] tmpls = new Template[types.length];
		for(int i=0; i < types.length; i++) {
			tmpls[i] = lookup(types[i]);
		}

		return gtmpl.build(tmpls);
	}

	private static boolean isAnnotated(Class<?> ao, Class<? extends Annotation> with) {
		return ao.getAnnotation(with) != null;
	}

}

