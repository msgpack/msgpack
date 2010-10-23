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

public interface Constants {
	String POSTFIX_TYPE_NAME_PACKER = "_$$_Packer";

	String POSTFIX_TYPE_NAME_UNPACKER = "_$$_Unpacker";

	String POSTFIX_TYPE_NAME_CONVERTER = "_$$_Converter";

	String POSTFIX_TYPE_NAME_TEMPLATE = "_$$_Template";

	String STRING_NAME_COMMA_SPACE = ", ";

	String STRING_NAME_LEFT_RIGHT_SQUARE_BRACKET = "[]";

	String CHAR_NAME_SPACE = " ";

	String CHAR_NAME_RIGHT_CURLY_BRACKET = "}";

	String CHAR_NAME_LEFT_CURLY_BRACKET = "{";

	String VARIABLE_NAME_TEMPLATES = "_$$_templates";

	String VARIABLE_NAME_PACKERS = "_$$_packers";

	String VARIABLE_NAME_CLIENT = "_$$_client";

	String METHOD_NAME_BOOLEANVALUE = "booleanValue";

	String METHOD_NAME_BYTEVALUE = "byteValue";

	String METHOD_NAME_SHORTVALUE = "shortValue";

	String METHOD_NAME_INTVALUE = "intValue";

	String METHOD_NAME_FLOATVALUE = "floatValue";

	String METHOD_NAME_LONGVALUE = "longValue";

	String METHOD_NAME_DOUBLEVALUE = "doubleValue";

	String METHOD_NAME_GETENUMCONSTANTS = "getEnumConstants";

	String METHOD_NAME_CONVERT = "convert";

	String METHOD_NAME_SETTEMPLATES = "setTemplates";

	String METHOD_NAME_SETMESSAGEPACKERS = "setMessagePackers";

	String METHOD_NAME_PACK = "pack";

	String METHOD_NAME_UNPACK = "unpack";

	String STATEMENT_PACKER_PACKERMETHODBODY_01 = "%s _$$_t = (%s)$2; ";

	String STATEMENT_PACKER_PACKERMETHODBODY_02 = "$1.packArray(%d); ";

	String STATEMENT_PACKER_PACKERMETHODBODY_03 = "_$$_packers[%d].pack($1, %s_$$_t.%s%s); ";

	String STATEMENT_PACKER_PACKERMETHODBODY_04 = "$1.pack(((java.lang.Enum)_$$_t).ordinal()); ";

	String STATEMENT_TMPL_UNPACKERMETHODBODY_01 = "%s _$$_t = new %s(); ";

	String STATEMENT_TMPL_UNPACKERMETHODBODY_02 = "$1.unpackArray(); ";

	String STATEMENT_TMPL_UNPACKERMETHODBODY_03 = "_$$_t.%s = %s(%s)_$$_templates[%d].unpack($1)%s; ";

	String STATEMENT_TMPL_UNPACKERMETHODBODY_04 = "return _$$_t; ";

	String STATEMENT_TMPL_UNPACKERMETHODBODY_05 = "int i = $1.unpackInt(); ";

	String STATEMENT_TMPL_UNPACKERMETHODBODY_06 = "return %s.class.getEnumConstants()[i]; ";

	String STATEMENT_TMPL_CONVERTMETHODBODY_01 = "%s _$$_ary = $1.asArray(); ";

	String STATEMENT_TMPL_CONVERTMETHODBODY_02 = "_$$_t.%s = %s(%s)_$$_templates[%d].convert(_$$_ary[%d])%s; ";

	String STATEMENT_TMPL_CONVERTMETHODBODY_03 = "int i = _$$_ary[0].asInt(); ";
}
