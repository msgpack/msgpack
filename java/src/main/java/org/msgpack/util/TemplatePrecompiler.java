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

import org.msgpack.template.TemplateBuildException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TemplatePrecompiler {
	private static final Logger LOG = LoggerFactory.getLogger(TemplatePrecompiler.class);

	public static void write(Class<?> target, String directoryName) {
		if (target.isEnum()) {
			throw new UnsupportedOperationException("Not supported yet.");
		} else {
			//TemplateBuilder.writeClass(target, directoryName);
		}
		LOG.info("finished writing .class file of template class for " + target.getName());
	}

	private String directoryName;

	private String[] classNames;

	private TemplatePrecompiler() {
	}

	private void parseOpts(final String[] args) {// TODO
		if (args.length == 0) {
			usage();
		}
	}

	private void usage() {// TODO
		System.err.println("java org.msgpack.template.TemplateClassWriter ");
		System.err.println("");
	}

	private void writeTemplateClasses() {
		ClassLoader cl = this.getClass().getClassLoader();// TODO
		for (String className : classNames) {
			Class<?> origClass = null;
			try {
				origClass = cl.loadClass(className);
			} catch (ClassNotFoundException e) {
				throw new TemplateBuildException(e);
			}
			write(origClass, directoryName);
		}
	}

	public static void main(final String[] args) throws Exception {
		TemplatePrecompiler writer = new TemplatePrecompiler();
		writer.parseOpts(args);
		writer.writeTemplateClasses();
	}
}
