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
package org.msgpack.template;

import java.io.IOException;
import java.lang.reflect.*;
import org.msgpack.*;

public class ReflectionTemplateBuilder extends TemplateBuilder {
	public ReflectionTemplateBuilder() {
	}

	public static abstract class ReflectionFieldEntry extends FieldEntry {
		public ReflectionFieldEntry(FieldEntry e) {
			super(e.getField(), e.getOption());
		}

		public abstract void pack(Object target, Packer pac) throws IOException;

		public abstract void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException;

		public abstract void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException;

		public void setNull(Object target) throws IllegalAccessException {
			getField().set(target, null);
		}
	}

	public static class ObjectFieldEntry extends ReflectionFieldEntry {
		public ObjectFieldEntry(FieldEntry e) {
			super(e);
		}

		public void pack(Object target, Packer pac) throws IOException {
			// TODO: call template
			pac.pack(target);
		}

		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			// TODO: call template
			Field f = getField();
			Class<Object> type = (Class<Object>)f.getType();
			Object fieldReference = f.get(target);
			Object valueReference = obj.convert(type, fieldReference);
			if(valueReference != fieldReference) {
				f.set(target, valueReference);
			}
		}

		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			// TODO: call template
			Field f = getField();
			Class<Object> type = (Class<Object>)f.getType();
			Object fieldReference = f.get(target);
			Object valueReference = pac.unpack(type, fieldReference);
			if(valueReference != fieldReference) {
				f.set(target, valueReference);
			}
		}
	}

	public static class BooleanFieldEntry extends ReflectionFieldEntry {
		public BooleanFieldEntry(FieldEntry e) {
			super(e);
		}
		public void pack(Object target, Packer pac) throws IOException {
			pac.pack((boolean)(Boolean)target);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			getField().setBoolean(target, obj.asBoolean());
		}
		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			getField().setBoolean(target, pac.unpackBoolean());
		}
	}

	public static class ByteFieldEntry extends ReflectionFieldEntry {
		public ByteFieldEntry(FieldEntry e) {
			super(e);
		}
		public void pack(Object target, Packer pac) throws IOException {
			pac.pack((byte)(Byte)target);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			getField().setByte(target, obj.asByte());
		}
		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			getField().setByte(target, pac.unpackByte());
		}
	}

	public static class ShortFieldEntry extends ReflectionFieldEntry {
		public ShortFieldEntry(FieldEntry e) {
			super(e);
		}
		public void pack(Object target, Packer pac) throws IOException {
			pac.pack((short)(Short)target);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			getField().setShort(target, obj.asShort());
		}
		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			getField().setShort(target, pac.unpackShort());
		}
	}

	public static class IntFieldEntry extends ReflectionFieldEntry {
		public IntFieldEntry(FieldEntry e) {
			super(e);
		}
		public void pack(Object target, Packer pac) throws IOException {
			pac.pack((int)(Integer)target);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			getField().setInt(target, obj.asInt());
		}
		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			getField().setInt(target, pac.unpackInt());
		}
	}

	public static class LongFieldEntry extends ReflectionFieldEntry {
		public LongFieldEntry(FieldEntry e) {
			super(e);
		}
		public void pack(Object target, Packer pac) throws IOException {
			pac.pack((long)(Long)target);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			getField().setLong(target, obj.asLong());
		}
		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			getField().setLong(target, pac.unpackLong());
		}
	}

	public static class FloatFieldEntry extends ReflectionFieldEntry {
		public FloatFieldEntry(FieldEntry e) {
			super(e);
		}
		public void pack(Object target, Packer pac) throws IOException {
			pac.pack((float)(Float)target);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			getField().setFloat(target, obj.asFloat());
		}
		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			getField().setFloat(target, pac.unpackFloat());
		}
	}

	public static class DoubleFieldEntry extends ReflectionFieldEntry {
		public DoubleFieldEntry(FieldEntry e) {
			super(e);
		}
		public void pack(Object target, Packer pac) throws IOException {
			pac.pack((double)(Double)target);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			getField().setDouble(target, obj.asDouble());
		}
		public void unpack(Object target, Unpacker pac) throws IOException, MessageTypeException, IllegalAccessException {
			getField().setDouble(target, pac.unpackDouble());
		}
	}

	private static class ReflectionTemplate extends AbstractTemplate {
		private Class<?> targetClass;
		private ReflectionFieldEntry[] entries;
		private int minimumArrayLength;

		public ReflectionTemplate(Class<?> targetClass, ReflectionFieldEntry[] entries) {
			this.targetClass = targetClass;
			this.entries = entries;
			for(int i=0; i < entries.length; i++) {
				if(entries[i].isRequired() || entries[i].isNullable()) {
					minimumArrayLength = i+1;
				}
			}
		}

		public void pack(Packer pk, Object target) throws IOException {
			try {
				pk.packArray(entries.length);
				for(ReflectionFieldEntry e : entries) {
					if(!e.isAvailable()) {
						pk.packNil();
						continue;
					}
					Object obj = e.getField().get(target);
					if(obj == null) {
						if(!e.isNullable() && !e.isOptional()) {
							throw new MessageTypeException();
						}
						pk.packNil();
					} else {
						pk.pack(obj);  // TODO: call template
					}
				}
			} catch (IOException e) {
				throw e;
			} catch (Exception e) {
				throw new MessageTypeException(e);
			}
		}

		public Object unpack(Unpacker pac, Object to) throws IOException, MessageTypeException {
			try {
				if(to == null) {
					to = targetClass.newInstance();
				}

				int length = pac.unpackArray();
				if(length < minimumArrayLength) {
					throw new MessageTypeException();
				}

				int i;
				for(i=0; i < minimumArrayLength; i++) {
					ReflectionFieldEntry e = entries[i];
					if(pac.tryUnpackNull()) {
						if(e.isRequired()) {
							// Requred + nil => exception
							throw new MessageTypeException();
						} else if(e.isOptional()) {
							// Optional + nil => keep default value
							continue;
						} else {  // Nullable
							// Nullable + nil => set null
							e.setNull(to);
							continue;
						}
					}
					e.unpack(to, pac);
				}

				int max = length < entries.length ? length : entries.length;
				for(; i < max; i++) {
					ReflectionFieldEntry e = entries[i];
					if(pac.tryUnpackNull()) {
						// this is Optional field becaue i >= minimumArrayLength
						// Optional + nil => keep default value
						continue;
					}
					e.unpack(to, pac);
				}

				// latter entries are all Optional + nil => keep default value

				for(; i < length; i++) {
					pac.unpackObject();
				}

				return to;

			} catch (IOException e) {
				throw e;
			} catch (Exception e) {
				throw new MessageTypeException(e);
			}
		}

		public Object convert(MessagePackObject from, Object to) throws MessageTypeException {
			try {
				if(to == null) {
					to = targetClass.newInstance();
				}

				MessagePackObject[] array = from.asArray();
				int length = array.length;
				if(length < minimumArrayLength) {
					throw new MessageTypeException();
				}

				int i;
				for(i=0; i < minimumArrayLength; i++) {
					ReflectionFieldEntry e = entries[i];
					MessagePackObject obj = array[i];
					if(obj.isNil()) {
						if(e.isRequired()) {
							// Requred + nil => exception
							throw new MessageTypeException();
						} else if(e.isOptional()) {
							// Optional + nil => keep default value
							continue;
						} else {  // Nullable
							// Nullable + nil => set null
							e.setNull(to);
							continue;
						}
					}
					e.convert(to, obj);
				}

				int max = length < entries.length ? length : entries.length;
				for(; i < max; i++) {
					ReflectionFieldEntry e = entries[i];
					MessagePackObject obj = array[i];
					if(obj.isNil()) {
						// this is Optional field becaue i >= minimumArrayLength
						// Optional + nil => keep default value
						continue;
					}
					e.convert(to, obj);
				}

				// latter entries are all Optional + nil => keep default value

				return to;

			} catch (Exception e) {
				throw new MessageTypeException(e);
			}
		}
	}

	public Template buildTemplate(Class<?> targetClass, FieldEntry[] entries) {
		for(FieldEntry e : entries) {
			Field f = e.getField();
			int mod = f.getModifiers();
			if(!Modifier.isPublic(mod)) {
				f.setAccessible(true);
			}
		}

		ReflectionFieldEntry[] res = new ReflectionFieldEntry[entries.length];
		for(int i=0; i < entries.length; i++) {
			FieldEntry e = entries[i];
			Class<?> type = e.getType();
			System.out.println(type);
			if(type.equals(boolean.class)) {
				res[i] = new BooleanFieldEntry(e);
			} else if(type.equals(byte.class)) {
				res[i] = new ByteFieldEntry(e);
			} else if(type.equals(short.class)) {
				res[i] = new ShortFieldEntry(e);
			} else if(type.equals(int.class)) {
				res[i] = new IntFieldEntry(e);
			} else if(type.equals(long.class)) {
				res[i] = new LongFieldEntry(e);
			} else if(type.equals(float.class)) {
				res[i] = new FloatFieldEntry(e);
			} else if(type.equals(double.class)) {
				res[i] = new DoubleFieldEntry(e);
			} else {
				res[i] = new ObjectFieldEntry(e);
			}
		}

		return new ReflectionTemplate(targetClass, res);
	}
}

