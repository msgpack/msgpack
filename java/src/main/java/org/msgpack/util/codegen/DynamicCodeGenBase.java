package org.msgpack.util.codegen;

import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import org.msgpack.CustomConverter;
import org.msgpack.CustomMessage;
import org.msgpack.MessageTypeException;
import org.msgpack.Template;
import org.msgpack.Templates;
import org.msgpack.annotation.MessagePackDelegate;
import org.msgpack.annotation.MessagePackMessage;
import org.msgpack.annotation.MessagePackOrdinalEnum;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class DynamicCodeGenBase implements BasicConstants {
	public static interface TemplateAccessor {
		void setTemplates(Template[] templates);
	}

	public static class TemplateAccessorImpl implements TemplateAccessor {
		public Template[] _$$_templates;

		public void setTemplates(Template[] _$$_tmpls) {
			_$$_templates = _$$_tmpls;
		}
	}

	private static Logger LOG = LoggerFactory
			.getLogger(DynamicCodeGenBase.class);

	public DynamicCodeGenBase() {
	}

	public void addPublicFieldDecl(StringBuilder sb, Class<?> type, String name) {
		addPublicFieldDecl(sb, type, name, 0);
	}

	public void addPublicFieldDecl(StringBuilder sb, Class<?> type,
			String name, int dim) {
		sb.append(KEYWORD_MODIFIER_PUBLIC);
		sb.append(CHAR_NAME_SPACE);
		sb.append(type.getName());
		for (int i = 0; i < dim; ++i) {
			sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		}
		sb.append(CHAR_NAME_SPACE);
		sb.append(name);
	}

	public void addPublicMethodDecl(StringBuilder sb, String mname,
			Class<?> returnType, Class<?>[] paramTypes, String[] anames,
			Class<?>[] exceptTypes, String methodBody) {
		int[] dims = new int[paramTypes.length];
		for (int i = 0; i < paramTypes.length; ++i) {
			dims[i] = 0;
		}
		addPublicMethodDecl(sb, mname, returnType, paramTypes, dims, anames,
				exceptTypes, methodBody);
	}

	public void addPublicMethodDecl(StringBuilder sb, String mname,
			Class<?> returnType, Class<?>[] paramTypes, int[] dims,
			String[] anames, Class<?>[] exceptTypes, String methodBody) {
		sb.append(KEYWORD_MODIFIER_PUBLIC);
		sb.append(CHAR_NAME_SPACE);
		sb.append(returnType.getName());
		sb.append(CHAR_NAME_SPACE);
		sb.append(mname);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		for (int i = 0; i < paramTypes.length; ++i) {
			sb.append(paramTypes[i].getName());
			for (int j = 0; j < dims[i]; ++j) {
				sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
				sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
			}
			sb.append(CHAR_NAME_SPACE);
			sb.append(anames[i]);
			if (i + 1 != paramTypes.length) {
				sb.append(CHAR_NAME_COMMA);
				sb.append(CHAR_NAME_SPACE);
			}
		}
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(CHAR_NAME_SPACE);
		if (exceptTypes.length != 0) {
			sb.append(KEYWORD_THROWS);
			sb.append(CHAR_NAME_SPACE);
			for (int i = 0; i < exceptTypes.length; ++i) {
				sb.append(exceptTypes[i].getName());
				if (i + 1 != exceptTypes.length) {
					sb.append(CHAR_NAME_COMMA);
					sb.append(CHAR_NAME_SPACE);
				}
			}
			sb.append(CHAR_NAME_SPACE);
		}
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		sb.append(methodBody);
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
	}

	public void insertSemicolon(StringBuilder sb) {
		// ;
		sb.append(CHAR_NAME_SEMICOLON);
		sb.append(CHAR_NAME_SPACE);
	}

	public void insertLocalVariableDecl(StringBuilder sb, Class<?> type,
			String name) {
		// int lv
		insertLocalVariableDecl(sb, type, name, 0);
	}

	public void insertLocalVariableDecl(StringBuilder sb, Class<?> type,
			String name, int dim) {
		// int[] lv
		int dim0 = dim + getArrayDim(type);
		Class<?> type0 = getArrayBaseType(type);
		sb.append(type0.getName());
		for (int i = 0; i < dim0; ++i) {
			sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		}
		sb.append(CHAR_NAME_SPACE);
		sb.append(name);
	}

	static int getArrayDim(Class<?> type) {
		if (type.isArray()) {
			return 1 + getArrayDim(type.getComponentType());
		} else {
			return 0;
		}
	}

	static Class<?> getArrayBaseType(Class<?> type) {
		if (type.isArray()) {
			return getArrayBaseType(type.getComponentType());
		} else {
			return type;
		}
	}
	
	public String arrayTypeToString(Class<?> type) {
		StringBuilder sb = new StringBuilder();
		int dim = getArrayDim(type);
		Class<?> t = getArrayBaseType(type);
		sb.append(t.getName());
		for (int i = 0; i < dim; ++i) {
			sb.append(CHAR_NAME_LEFT_SQUARE_BRACKET);
			sb.append(CHAR_NAME_RIGHT_SQUARE_BRACKET);
		}
		return sb.toString();
	}

	public void insertValueInsertion(StringBuilder sb, String expr) {
		// = expr
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
		sb.append(expr);
	}

	public void insertInsertion(StringBuilder sb) {
		// =
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_EQUAL);
		sb.append(CHAR_NAME_SPACE);
	}

	public void insertFieldAccess(StringBuilder sb, String target, String field) {
		// target.field
		sb.append(target);
		sb.append(CHAR_NAME_DOT);
		sb.append(field);
	}

	public void insertDefaultConsCall(StringBuilder sb, Class<?> type) {
		// new tname()
		insertConsCall(sb, type, null);
	}

	public void insertConsCall(StringBuilder sb, Class<?> type, String expr) {
		// new tname(expr)
		sb.append(KEYWORD_NEW);
		sb.append(CHAR_NAME_SPACE);
		sb.append(type.getName());
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		if (expr != null) {
			sb.append(expr);
		}
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
	}

	public void insertMethodCall(StringBuilder sb, String tname, String mname,
			String[] anames) {
		// tname.mname(anames[0], anames[1], ...)
		int len = anames.length;
		sb.append(tname);
		sb.append(CHAR_NAME_DOT);
		sb.append(mname);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		for (int i = 0; i < len; ++i) {
			sb.append(anames[i]);
			if (i + 1 != len) {
				sb.append(CHAR_NAME_COMMA);
				sb.append(CHAR_NAME_SPACE);
			}
		}
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
	}

	public void insertTypeCast(StringBuilder sb, Class<?> type) {
		// (type)
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(type.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
	}

	public void insertTypeCast(StringBuilder sb, Class<?> type, String varName) {
		// ((type)var)
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(CHAR_NAME_LEFT_PARENTHESIS);
		sb.append(type.getName());
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
		sb.append(varName);
		sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
	}

	public void insertReturnStat(StringBuilder sb, String expr) {
		// return expr
		sb.append(KEYWORD_RETURN);
		sb.append(CHAR_NAME_SPACE);
		sb.append(expr);
	}

	public void insertTypeConvToObjectType(StringBuilder sb, Class<?> type,
			String expr) throws DynamicCodeGenException {
		if (type.isPrimitive()) { // primitive type
			insertConsCall(sb, primitiveTypeToWrapperType(type), expr);
		} else { // reference type
			sb.append(expr);
		}
	}

	public void insertTryCatchBlocks(StringBuilder sb, String tryBody,
			List<Class<?>> types, List<String> names, List<String> catchBodies) {
		int len = types.size();
		sb.append(KEYWORD_TRY);
		sb.append(CHAR_NAME_SPACE);
		sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		sb.append(tryBody);
		sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
		sb.append(CHAR_NAME_SPACE);
		for (int i = 0; i < len; ++i) {
			sb.append(KEYWORD_CATCH);
			sb.append(CHAR_NAME_SPACE);
			sb.append(CHAR_NAME_LEFT_PARENTHESIS);
			sb.append(types.get(i).getName());
			sb.append(CHAR_NAME_SPACE);
			sb.append(names.get(i));
			sb.append(CHAR_NAME_RIGHT_PARENTHESIS);
			sb.append(CHAR_NAME_SPACE);
			sb.append(CHAR_NAME_LEFT_CURLY_BRACKET);
			sb.append(CHAR_NAME_SPACE);
			sb.append(catchBodies.get(i));
			sb.append(CHAR_NAME_RIGHT_CURLY_BRACKET);
			sb.append(CHAR_NAME_SPACE);
		}
	}
	
	public Class<?> primitiveTypeToWrapperType(Class<?> type) {
		if (type.equals(boolean.class)) {
			return Boolean.class;
		} else if (type.equals(byte.class)) {
			return Byte.class;
		} else if (type.equals(short.class)) {
			return Short.class;
		} else if (type.equals(int.class)) {
			return Integer.class;
		} else if (type.equals(long.class)) {
			return Long.class;
		} else if (type.equals(float.class)) {
			return Float.class;
		} else if (type.equals(double.class)) {
			return Double.class;
		} else {
			throw new MessageTypeException("Type error: " + type.getName());
		}
	}
	
	public String getPrimTypeValueMethodName(Class<?> type) {
		if (type.equals(boolean.class)) {
			return METHOD_NAME_BOOLEANVALUE;
		} else if (type.equals(byte.class)) {
			return METHOD_NAME_BYTEVALUE;
		} else if (type.equals(short.class)) {
			return METHOD_NAME_SHORTVALUE;
		} else if (type.equals(int.class)) {
			return METHOD_NAME_INTVALUE;
		} else if (type.equals(long.class)) {
			return METHOD_NAME_LONGVALUE;
		} else if (type.equals(float.class)) {
			return METHOD_NAME_FLOATVALUE;
		} else if (type.equals(double.class)) {
			return METHOD_NAME_DOUBLEVALUE;
		} else {
			throw new MessageTypeException("Type error: " + type.getName());
		}
	}
	public String getUnpackMethodName(Class<?> c)
			throws DynamicCodeGenException {
		if (c.equals(boolean.class) || c.equals(Boolean.class)) {
			return METHOD_NAME_UNPACKBOOLEAN;
		} else if (c.equals(byte.class) || c.equals(Byte.class)) {
			return METHOD_NAME_UNPACKBYTE;
		} else if (c.equals(short.class) || c.equals(Short.class)) {
			return METHOD_NAME_UNPACKSHORT;
		} else if (c.equals(int.class) || c.equals(Integer.class)) {
			return METHOD_NAME_UNPACKINT;
		} else if (c.equals(float.class) || c.equals(Float.class)) {
			return METHOD_NAME_UNPACKFLOAT;
		} else if (c.equals(long.class) || c.equals(Long.class)) {
			return METHOD_NAME_UNPACKLONG;
		} else if (c.equals(double.class) || c.equals(Double.class)) {
			return METHOD_NAME_UNPACKDOUBLE;
		} else if (c.equals(String.class)) {
			return METHOD_NAME_UNPACKSTRING;
		} else if (c.equals(byte[].class)) {
			return METHOD_NAME_UNPACKBYTEARRAY;
		} else if (c.equals(BigInteger.class)) {
			return METHOD_NAME_UNPACKBIGINTEGER;
		} else if (List.class.isAssignableFrom(c)) {
			return METHOD_NAME_UNPACK;
		} else if (Map.class.isAssignableFrom(c)) {
			return METHOD_NAME_UNPACK;
		} else {
			throw new DynamicCodeGenException("Type error: " + c.getName());
		}
	}

	public String getAsMethodName(Class<?> c) {
		if (c.equals(boolean.class) || c.equals(Boolean.class)) {
			return METHOD_NAME_ASBOOLEAN;
		} else if (c.equals(byte.class) || c.equals(Byte.class)) {
			return METHOD_NAME_ASBYTE;
		} else if (c.equals(short.class) || c.equals(Short.class)) {
			return METHOD_NAME_ASSHORT;
		} else if (c.equals(int.class) || c.equals(Integer.class)) {
			return METHOD_NAME_ASINT;
		} else if (c.equals(float.class) || c.equals(Float.class)) {
			return METHOD_NAME_ASFLOAT;
		} else if (c.equals(long.class) || c.equals(Long.class)) {
			return METHOD_NAME_ASLONG;
		} else if (c.equals(double.class) || c.equals(Double.class)) {
			return METHOD_NAME_ASDOUBLE;
		} else if (c.equals(String.class)) {
			return METHOD_NAME_ASSTRING;
		} else if (c.equals(byte[].class)) {
			return METHOD_NAME_ASBYTEARRAY;
		} else if (c.equals(BigInteger.class)) {
			return METHOD_NAME_ASBIGINTEGER;
		} else if (List.class.isAssignableFrom(c)) {
			return METHOD_NAME_ASLIST;
		} else if (Map.class.isAssignableFrom(c)) {
			return METHOD_NAME_ASMAP;
		} else {
			throw new DynamicCodeGenException("Type error: " + c.getName());
		}
	}

	public Template createTemplate(Type t) {
		if (t.getClass().equals(Class.class)) {
			Class<?> c = (Class<?>) t;
			if (c.equals(boolean.class) || c.equals(Boolean.class)) {
				return Templates.tBoolean();
			} else if (c.equals(byte.class) || c.equals(Byte.class)) {
				return Templates.tByte();
			} else if (c.equals(short.class) || c.equals(Short.class)) {
				return Templates.tShort();
			} else if (c.equals(int.class) || c.equals(Integer.class)) {
				return Templates.tInteger();
			} else if (c.equals(float.class) || c.equals(Float.class)) {
				return Templates.tFloat();
			} else if (c.equals(long.class) || c.equals(Long.class)) {
				return Templates.tLong();
			} else if (c.equals(double.class) || c.equals(Double.class)) {
				return Templates.tDouble();
			} else if (c.equals(String.class)) {
				return Templates.tString();
			} else if (c.equals(BigInteger.class)) {
				return Templates.tBigInteger();
			} else if (CustomConverter.isRegistered(c)) {
				return (Template) CustomConverter.get(c);
			} else if (CustomMessage.isAnnotated(c, MessagePackMessage.class)) {
				// @MessagePackMessage
				Template tmpl = DynamicCodeGenTemplate.create(c);
				CustomMessage.registerTemplate(c, tmpl);
				return tmpl;
			} else if (CustomMessage.isAnnotated(c, MessagePackDelegate.class)) {
				// FIXME DelegatePacker
				UnsupportedOperationException e = new UnsupportedOperationException(
						"not supported yet. : " + c.getName());
				LOG.error(e.getMessage(), e);
				throw e;
			} else if (CustomMessage.isAnnotated(c,
					MessagePackOrdinalEnum.class)) {
				// @MessagePackOrdinalEnum
				Template tmpl = DynamicCodeGenOrdinalEnumTemplate.create(c);
				CustomMessage.registerTemplate(c, tmpl);
				return tmpl;
			} else {
				throw new DynamicCodeGenException("Type error: "
						+ ((Class<?>) t).getName());
			}
		} else if (t instanceof GenericArrayType) {
			GenericArrayType gat = (GenericArrayType) t;
			Type gct = gat.getGenericComponentType();
			if (gct.equals(byte.class)) {
				return Templates.tByteArray();
			} else {
				throw new DynamicCodeGenException("Not supported yet: " + gat);
			}
		} else if (t instanceof ParameterizedType) {
			ParameterizedType pt = (ParameterizedType) t;
			Class<?> rawType = (Class<?>) pt.getRawType();
			if (rawType.equals(List.class)) {
				Type[] ats = pt.getActualTypeArguments();
				return Templates.tList(createTemplate(ats[0]));
			} else if (rawType.equals(Map.class)) {
				Type[] ats = pt.getActualTypeArguments();
				return Templates.tMap(createTemplate(ats[0]),
						createTemplate(ats[1]));
			} else {
				throw new DynamicCodeGenException("Type error: "
						+ t.getClass().getName());
			}
		} else {
			throw new DynamicCodeGenException("Type error: "
					+ t.getClass().getName());
		}
	}
}
