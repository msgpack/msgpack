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
package org.msgpack.util;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import javax.tools.StandardLocation;
import javax.tools.ToolProvider;

import org.msgpack.template.builder.JavassistTemplateBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class is a template precompiler, which is used for saving templates
 * that <code>TemplateBuilder</code> generated.  It saves templates as .class files.
 * Application enables to load the .class files and use templates.
 *
 */
public class TemplatePrecompiler {

	private static final Logger LOG = LoggerFactory.getLogger(TemplatePrecompiler.class);

	public static final String DEST = "msgpack.template.destdir";

	public static final String DEFAULT_DEST = ".";

	public static void saveTemplates(final String[] classNames) throws IOException, ClassNotFoundException {
		List<String> ret = new ArrayList<String>();
		for (String className : classNames) {
			matchClassNames(ret, className);
		}
		List<Class<?>> ret0 = toClass(ret);
		for (Class<?> c : ret0) {
			saveTemplateClass(c);
		}
	}

	@SuppressWarnings("serial")
	private static void matchClassNames(List<String> ret, final String className) throws IOException {
		String packageName = className.substring(0, className.lastIndexOf('.'));
		String relativedName = className.substring(className.lastIndexOf('.') + 1, className.length());
		String patName = relativedName.replace("*", "(\\w+)");
		Pattern pat = Pattern.compile(patName);

		JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
		JavaFileManager fm = compiler.getStandardFileManager(
		    new DiagnosticCollector<JavaFileObject>(), null, null);
		HashSet<JavaFileObject.Kind> kind = new HashSet<JavaFileObject.Kind>(){{
		    add(JavaFileObject.Kind.CLASS);
		}};

		for (JavaFileObject f : fm.list(StandardLocation.PLATFORM_CLASS_PATH, packageName, kind, false)) {
			String relatived0 = f.getName();
			String name0 = relatived0.substring(0, relatived0.length() - ".class".length());
			Matcher m = pat.matcher(name0);
			if (m.matches()) {
				String name = packageName + '.' + name0;
				if (!ret.contains(name)) {
					ret.add(name);
				}
			}
		}
	}

	private static List<Class<?>> toClass(List<String> classNames) throws ClassNotFoundException {
		List<Class<?>> ret = new ArrayList<Class<?>>(classNames.size());
		ClassLoader cl = TemplatePrecompiler.class.getClassLoader();
		for (String className : classNames) {
			Class<?> c = cl.loadClass(className);
			ret.add(c);
		}
		return ret;
	}

	public static void saveTemplateClasses(Class<?>[] targetClasses) throws IOException {
		for (Class<?> c : targetClasses) {
			saveTemplateClass(c);
		}
	}

	public static void saveTemplateClass(Class<?> targetClass) throws IOException {
		LOG.info("Saving template of " + targetClass.getName() + "...");
		Properties props = System.getProperties();
		String distDirName = getDirName(props, DEST, DEFAULT_DEST);
		if (targetClass.isEnum()) {
			throw new UnsupportedOperationException("Not supported enum type yet: " + targetClass.getName());
		} else {
			new JavassistTemplateBuilder().writeTemplate(targetClass, distDirName);
		}
		LOG.info("Saved .class file of template class of " + targetClass.getName());
	}

	private static String getDirName(Properties props, String dirName, String defaultDirName)
			throws IOException {
		String dName = props.getProperty(dirName, defaultDirName);
		File d = new File(dName);
		if (!d.isDirectory() && !d.exists()) {
			throw new IOException("Directory not exists: " + dName);
		}
		return d.getAbsolutePath();
	}

	public static void main(final String[] args) throws Exception {
		TemplatePrecompiler.saveTemplates(args);
	}
}
