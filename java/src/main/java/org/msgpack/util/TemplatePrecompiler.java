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
import java.util.Properties;

import org.msgpack.template.builder.BuilderSelectorRegistry;
import org.msgpack.template.builder.JavassistTemplateBuilder;
import org.msgpack.template.builder.TemplateBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TemplatePrecompiler {
	private static final Logger LOG = LoggerFactory.getLogger(TemplatePrecompiler.class);

	//public static final String SRC = "msgpack.template.srcdir";

	public static final String DIST = "msgpack.template.distdir";

	//public static final String DEFAULT_SRC = ".";

	public static final String DEFAULT_DIST = ".";

	private static TemplatePrecompiler INSTANCE = null;

	private TemplatePrecompiler() {
	}

	public static void saveTemplates(final String[] classFileNames) throws IOException {
		throw new UnsupportedOperationException("Not supported yet.");// TODO
	}

	public static void saveTemplateClass(Class<?> targetClass) throws IOException {
		if (INSTANCE != null) {
			INSTANCE = new TemplatePrecompiler();
		}
		LOG.info("Saving template of " + targetClass.getName() + "...");
		Properties props = System.getProperties();
		String distDirName = getDirName(props, DIST, DEFAULT_DIST);
		if (targetClass.isEnum()) {
			throw new UnsupportedOperationException("Enum not supported yet: " + targetClass.getName());
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
