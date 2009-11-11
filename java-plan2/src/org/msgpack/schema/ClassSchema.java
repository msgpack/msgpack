package org.msgpack.schema;

import java.util.List;

public abstract class ClassSchema extends Schema {
	protected String namespace;
	protected List<String> imports;

	public ClassSchema(String name, String namespace, List<String> imports)
	{
		super(name);
		this.namespace = namespace;
		this.imports = imports;
	}

	public String getNamespace()
	{
		return namespace;
	}

	public List<String> getImports()
	{
		return imports;
	}

	void setNamespace(String namespace)
	{
		this.namespace = namespace;
	}

	void setImports(List<String> imports)
	{
		this.imports = imports;
	}

	public abstract List<? extends FieldSchema> getFields();
	public abstract Object newInstance();
}

