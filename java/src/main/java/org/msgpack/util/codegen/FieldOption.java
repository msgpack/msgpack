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
