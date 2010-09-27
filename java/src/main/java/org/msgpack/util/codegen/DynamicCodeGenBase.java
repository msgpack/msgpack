package org.msgpack.util.codegen;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

public class DynamicCodeGenBase implements BasicConstants {
    public DynamicCodeGenBase() {
    }

    public void insertSemicolon(StringBuilder sb) {
        sb.append(CHAR_NAME_SEMICOLON);
        sb.append(CHAR_NAME_SPACE);
    }

    public void insertPublicFieldDecl(StringBuilder sb, Class<?> type,
            String name) {
        sb.append(KEYWORD_MODIFIER_PUBLIC);
        sb.append(CHAR_NAME_SPACE);
        sb.append(type.getName());
        sb.append(CHAR_NAME_SPACE);
        sb.append(name);
    }

    public void insertLocalVariableDecl(StringBuilder sb, Class<?> type,
            String name) {
        sb.append(type.getName());
        sb.append(CHAR_NAME_SPACE);
        sb.append(name);
    }
    
    public void insertValueInsertion(StringBuilder sb, String expr) {
        //  = expr
        sb.append(CHAR_NAME_SPACE);
        sb.append(CHAR_NAME_EQUAL);
        sb.append(CHAR_NAME_SPACE);
        sb.append(expr);
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
    
    public void insertTypeConvToObjectType(StringBuilder sb, Class<?> type,
            String expr) throws DynamicCodeGenException {
        if (type.isPrimitive()) { // primitive type
            if (type.equals(boolean.class)) {
                // new Boolean(expr)
                insertConsCall(sb, Boolean.class, expr);
            } else if (type.equals(byte.class)) {
                insertConsCall(sb, Byte.class, expr);
            } else if (type.equals(short.class)) {
                insertConsCall(sb, Short.class, expr);
            } else if (type.equals(int.class)) {
                insertConsCall(sb, Integer.class, expr);
            } else if (type.equals(long.class)) {
                insertConsCall(sb, Long.class, expr);
            } else if (type.equals(float.class)) {
                insertConsCall(sb, Float.class, expr);
            } else if (type.equals(double.class)) {
                insertConsCall(sb, Double.class, expr);
            } else {
                throw new DynamicCodeGenException("Type error: "
                        + type.getName());
            }
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

    public String getAsMethod(Class<?> c) throws DynamicCodeGenException {
        if (c.equals(boolean.class)) {
            return METHOD_NAME_ASBOOLEAN;
        } else if (c.equals(byte.class)) {
            return METHOD_NAME_ASBYTE;
        } else if (c.equals(short.class)) {
            return METHOD_NAME_ASSHORT;
        } else if (c.equals(int.class)) {
            return METHOD_NAME_ASINT;
        } else if (c.equals(float.class)) {
            return METHOD_NAME_ASFLOAT;
        } else if (c.equals(long.class)) {
            return METHOD_NAME_ASLONG;
        } else if (c.equals(double.class)) {
            return METHOD_NAME_ASDOUBLE;
        } else if (c.equals(Boolean.class)) {
            return METHOD_NAME_ASBOOLEAN;
        } else if (c.equals(Byte.class)) {
            return METHOD_NAME_ASBYTE;
        } else if (c.equals(Short.class)) {
            return METHOD_NAME_ASSHORT;
        } else if (c.equals(Integer.class)) {
            return METHOD_NAME_ASINT;
        } else if (c.equals(Float.class)) {
            return METHOD_NAME_ASFLOAT;
        } else if (c.equals(Long.class)) {
            return METHOD_NAME_ASLONG;
        } else if (c.equals(Double.class)) {
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
}
