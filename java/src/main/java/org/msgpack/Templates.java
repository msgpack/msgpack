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
package org.msgpack;

import org.msgpack.template.*;

public class Templates {
	public static Template tNullable(Template elementTemplate) {
		return new NullableTemplate(elementTemplate);
	}


	public static final Template TAny = AnyTemplate.getInstance();
	public static Template tAny() {
		return TAny;
	}


	public static Template tList(Template elementTemplate) {
		return new ListTemplate(elementTemplate);
	}

	public static Template tMap(Template keyTemplate, Template valueTemplate) {
		return new MapTemplate(keyTemplate, valueTemplate);
	}

	public static Template tCollection(Template elementTemplate) {
		return new CollectionTemplate(elementTemplate);
	}

	public static Template tClass(Class target) {
		Template tmpl = TemplateRegistry.lookup(target);
		if(tmpl == null) {
			// FIXME
		}
		return tmpl;
	}

	public static final Template TByte = ByteTemplate.getInstance();
	public static Template tByte() {
		return TByte;
	}

	public static final Template TShort = ShortTemplate.getInstance();
	public static Template tShort() {
		return TShort;
	}

	public static final Template TInteger = IntegerTemplate.getInstance();
	public static Template tInteger() {
		return TInteger;
	}

	public static final Template TLong = LongTemplate.getInstance();
	public static Template tLong() {
		return TLong;
	}

	public static final Template TBigInteger = BigIntegerTemplate.getInstance();
	public static Template tBigInteger() {
		return TBigInteger;
	}

	public static final Template TFloat = FloatTemplate.getInstance();
	public static Template tFloat() {
		return TFloat;
	}

	public static final Template TDouble = DoubleTemplate.getInstance();
	public static Template tDouble() {
		return TDouble;
	}

	public static final Template TBoolean = BooleanTemplate.getInstance();
	public static Template tBoolean() {
		return TBoolean;
	}

	public static final Template TString = StringTemplate.getInstance();
	public static Template tString() {
		return TString;
	}

	public static final Template TByteArray = ByteArrayTemplate.getInstance();
	public static Template tByteArray() {
		return TByteArray;
	}

	public static final Template TByteBuffer = ByteBufferTemplate.getInstance();
	public static Template tByteBuffer() {
		return TByteBuffer;
	}
}

