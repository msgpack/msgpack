package org.msgpack.impl;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import org.msgpack.schema.*;

public final class SpecificObjectBuilder implements ObjectBuilder {
	private int top;
	private Schema schema;

	public SpecificObjectBuilder(Schema schema)
	{
		this.top = 0;
		this.schema = schema;
	}

	void setSchema(Schema s)
	{
		schema = s;
	}

	Schema swapSchema(Schema s)
	{
		Schema old = schema;
		schema = s;
		return old;
	}

	@Override
	public Object createNil()
	{
		return schema.createNil();
	}

	@Override
	public Object createBoolean(boolean v)
	{
		return schema.createBoolean(v);
	}

	@Override
	public Object createByte(byte v)
	{
		return schema.createByte(v);
	}

	@Override
	public Object createShort(short v)
	{
		return schema.createShort(v);
	}

	@Override
	public Object createInt(int v)
	{
		return schema.createInt(v);
	}

	@Override
	public Object createLong(long v)
	{
		return schema.createLong(v);
	}

	@Override
	public Object createFloat(float v)
	{
		return schema.createFloat(v);
	}

	@Override
	public Object createDouble(double v)
	{
		return schema.createDouble(v);
	}

	@Override
	public Object createRaw(byte[] b, int offset, int length)
	{
		return schema.createRaw(b, offset, length);
	}

	@Override
	public ArrayBuilder createArray(int length)
	{
		if(schema instanceof ClassSchema) {
			return new ClassBuilder(length, (ClassSchema)schema, this);
		}
		ArraySchema as = (ArraySchema)schema;
		return new SpecificArrayBuilder(length, as.getElementType(), this);
	}

	@Override
	public MapBuilder createMap(int length)
	{
		MapSchema ms = (MapSchema)schema;
		return new SpecificMapBuilder(length, ms.getKeyType(), ms.getValueType(), this);
	}
}

final class SpecificArrayBuilder implements ArrayBuilder {
	private ArrayList a;
	private SpecificObjectBuilder builder;
	private Schema parentSchema;

	SpecificArrayBuilder(int length, Schema elementSchema, SpecificObjectBuilder builder)
	{
		this.a = new ArrayList(length);
		this.builder = builder;
		this.parentSchema = builder.swapSchema(elementSchema);
	}

	public void add(Object element)
	{
		a.add(element);
	}

	public Object finish()
	{
		builder.swapSchema(parentSchema);
		return a;
	}
}

final class SpecificMapBuilder implements MapBuilder {
	private HashMap m;
	private Object key;
	private Schema keySchema;
	private Schema valueSchema;
	private SpecificObjectBuilder builder;
	private Schema parentSchema;

	SpecificMapBuilder(int length, Schema keySchema, Schema valueSchema, SpecificObjectBuilder builder)
	{
		this.m = new HashMap(length);
		this.keySchema = keySchema;
		this.valueSchema = valueSchema;
		this.builder = builder;
		this.parentSchema = builder.swapSchema(keySchema);
	}

	@Override
	public void putKey(Object key)
	{
		this.key = key;
		this.builder.setSchema(valueSchema);
	}

	@Override
	public void putValue(Object value)
	{
		m.put(this.key, value);
		this.key = null;
		this.builder.setSchema(keySchema);
	}

	@Override
	public Object finish()
	{
		builder.swapSchema(parentSchema);
		return m;
	}
}

final class ClassBuilder implements ArrayBuilder {
	private Object object;
	private int index;
	private List<? extends FieldSchema> fields;
	private SpecificObjectBuilder builder;
	private Schema parentSchema;

	ClassBuilder(int length, ClassSchema schema, SpecificObjectBuilder builder)
	{
		this.object = schema.newInstance();
		this.index = 0;
		this.fields = schema.getFields();
		this.builder = builder;
		this.parentSchema = builder.swapSchema(fields.get(0).getType());
		// FIXME check length
	}

	@Override
	public void add(Object element)
	{
		FieldSchema f = fields.get(index++);  // FIXME check fields.size
		f.setFieldValue(object, element);  // XXX FIXME debug
		if(fields.size() > index) {
			builder.setSchema( fields.get(index).getType() );
		} else {
			builder.setSchema( null );
			// FIXME: builder.setSchema(new InvalidFieldSchema);
		}
	}

	@Override
	public Object finish()
	{
		builder.swapSchema(parentSchema);
		return object;
	}
}

