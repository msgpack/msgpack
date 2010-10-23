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
package org.msgpack.util.codegen;

import org.msgpack.Template;

public class FieldOption {

	private static final String NULL_ERR_MSG = "param is FieldOption is null.";

	String name;

	Template tmpl;

	public FieldOption(final String name, final Template tmpl) {
		if (name == null) {
			throw new NullPointerException(String.format("%s %s", new Object[] {
					"1st", NULL_ERR_MSG }));
		}
		if (tmpl == null) {
			throw new NullPointerException(String.format("%s %s", new Object[] {
					"2nd", NULL_ERR_MSG }));
		}
		this.name = name;
		this.tmpl = tmpl;
	}
}
