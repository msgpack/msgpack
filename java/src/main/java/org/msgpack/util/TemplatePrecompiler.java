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
import org.msgpack.template.builder.TemplateBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TemplatePrecompiler {
	private static final Logger LOG = LoggerFactory.getLogger(TemplatePrecompiler.class);

	//private static final String SRC = "msgpack.template.srcdir";

	private static final String DIST = "msgpack.template.distdir";

	//private static final String DEFAULT_SRC = ".";

	private static final String DEFAULT_DIST = ".";

	private TemplatePrecompiler() {
	}

	public void saveTemplates(final String[] classFileNames) throws IOException {
		throw new UnsupportedOperationException("Not supported yet.");// TODO
	}

	public void saveTemplateClass(Class<?> targetClass) throws IOException {
		LOG.info("Saving template of " + targetClass.getName() + "...");
		Properties props = System.getProperties();
		String distDirName = getDirName(props, DIST, DEFAULT_DIST);
		if (targetClass.isEnum()) {
			throw new UnsupportedOperationException("Enum not supported yet: " + targetClass.getName());
		} else {
			TemplateBuilder builder = BuilderSelectorRegistry.getInstance().select(targetClass);
			builder.writeTemplate(targetClass, distDirName);
		}
		LOG.info("Saved .class file of template class of " + targetClass.getName());
	}

	private String getDirName(Properties props, String dirName, String defaultDirName)
			throws IOException {
		String dName = props.getProperty(dirName, defaultDirName);
		File d = new File(dName);
		if (!d.isDirectory() && !d.exists()) {
			throw new IOException("Directory not exists: " + dName);
		}
		return d.getAbsolutePath();
	}

	public static void main(final String[] args) throws Exception {
		TemplatePrecompiler compiler = new TemplatePrecompiler();// TODO
		compiler.saveTemplates(args);
	}
}
