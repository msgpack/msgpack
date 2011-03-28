package org.msgpack.template;

import java.io.IOException;
import java.lang.reflect.Field;

import org.msgpack.AbstractTemplate;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.template.ReflectionTemplateBuilder.BooleanFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.ByteFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.DoubleFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.FloatFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.IntFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.LongFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.NullFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.ObjectFieldEntry;
import org.msgpack.template.ReflectionTemplateBuilder.ShortFieldEntry;
import org.msgpack.template.builder.CustomTemplateBuilder;

/**
 * Class for building java reflection template builder for java beans class.
 * @author takeshita
 *
 */
public class BeansReflectionTemplateBuilder extends CustomTemplateBuilder{

	IFieldEntryReader reader = new BeansFieldEntryReader();
	
	public BeansReflectionTemplateBuilder(){}

	@Override
	public IFieldEntryReader getFieldEntryReader(){
		return reader;
	}
	
	static class ReflectionEntry{
		BeansFieldEntry entry;
		public ReflectionEntry(BeansFieldEntry entry){
			this.entry = entry;
		}
		
		public void pack(Object value , Packer packer) throws IOException{
			packer.pack(value);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			entry.set(target, obj.convert(entry.getType()));
		}
		
		public void unpack(Object target, Unpacker unpacker) throws IOException, MessageTypeException, IllegalAccessException {
			entry.set(target, unpacker.unpack(entry.getType()));
		}
		
		public void setNull(Object target){
			entry.set(target, null);
		}
		
		public boolean isRequired(){
			return entry.isRequired();
		}
		public boolean isNullable(){
			return entry.isNullable();
		}
		public boolean isAvailable(){
			return entry.isAvailable();
		}
		public boolean isOptional(){
			return entry.isOptional();
		}
		public Object get(Object target){
			return entry.get(target);
		}
		
	}
	
	static class ObjectFieldEntry extends ReflectionEntry{
		Template template;
		public ObjectFieldEntry(BeansFieldEntry entry,Template template){
			super(entry);
			this.template = template;
		}
		public void pack(Object value , Packer packer) throws IOException{
			template.pack(packer,value);
		}
		public void convert(Object target, MessagePackObject obj) throws MessageTypeException, IllegalAccessException {
			Class<Object> type = (Class<Object>)entry.getType();
			Object fieldReference = entry.get(target);
			Object valueReference = template.convert(obj, fieldReference);
			if(valueReference != fieldReference) {
				entry.set(target, valueReference);
			}
		}
		
		public void unpack(Object target, Unpacker unpacker) throws IOException, MessageTypeException, IllegalAccessException {

			Class<Object> type = (Class<Object>)entry.getType();
			Object fieldReference = entry.get(target);
			Object valueReference = template.unpack(unpacker, fieldReference);
			if(valueReference != fieldReference) {
				entry.set(target, valueReference);
			}
		}
	}
	
	static class BeansReflectionTemplate extends AbstractTemplate{
		
		Class<?> targetClass;
		ReflectionEntry[] entries = null;
		protected int minimumArrayLength;
		
		public BeansReflectionTemplate(
				Class<?> targetClass,
				ReflectionEntry[] entries){
			this.targetClass = targetClass;
			this.entries = entries;
			this.minimumArrayLength = 0;
			for(int i=0; i < entries.length; i++) {
				ReflectionEntry e = entries[i];
				if(e.isRequired() || e.isNullable()) {
					this.minimumArrayLength = i+1;
				}
			}
		}
		

		@Override
		public void pack(Packer pk, Object target) throws IOException {
			
			pk.packArray(entries.length);
			for(ReflectionEntry e : entries){
				if(!e.isAvailable()){
					pk.packNil();
					continue;
				}
				Object obj = e.get(target);
				if(obj == null) {
					if(!e.isNullable() && !e.isOptional()) {
						throw new MessageTypeException();
					}
					pk.packNil();
				} else {
					pk.pack(obj);
				}
			}
			
		}
		@Override
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
					ReflectionEntry e = entries[i];
					if(!e.isAvailable()) {
						pac.unpackObject();
						continue;
					}

					if(pac.tryUnpackNull()) {
						if(e.isRequired()) {
							// Required + nil => exception
							throw new MessageTypeException();
						} else if(e.isOptional()) {
							// Optional + nil => keep default value
						} else {  // Nullable
							// Nullable + nil => set null
							e.setNull(to);
						}
					} else {
						e.unpack(to,pac);
						//e.set(to, pac.unpack(e.getType()));
					}
				}

				int max = length < entries.length ? length : entries.length;
				for(; i < max; i++) {
					ReflectionEntry e = entries[i];
					if(!e.isAvailable()) {
						pac.unpackObject();
						continue;
					}

					if(pac.tryUnpackNull()) {
						// this is Optional field becaue i >= minimumArrayLength
						// Optional + nil => keep default value
					} else {
						e.unpack(to, pac);
						//e.set(to, pac.unpack(e.getType()));
					}
				}

				// latter entries are all Optional + nil => keep default value

				for(; i < length; i++) {
					pac.unpackObject();
				}

				return to;

			} catch (MessageTypeException e) {
				throw e;
			} catch (IOException e) {
				throw e;
			} catch (Exception e) {
				throw new MessageTypeException(e);
			}
		}

		@Override
		public Object convert(MessagePackObject from, Object to)
				throws MessageTypeException {
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
					ReflectionEntry e = entries[i];
					if(!e.isAvailable()) {
						continue;
					}

					MessagePackObject obj = array[i];
					if(obj.isNil()) {
						if(e.isRequired()) {
							// Required + nil => exception
							throw new MessageTypeException();
						} else if(e.isOptional()) {
							// Optional + nil => keep default value
						} else {  // Nullable
							// Nullable + nil => set null
							e.setNull(to);
							//e.set(to,null);
						}
					} else {
						e.convert(to, obj);
						//e.set(to, from.convert(e.getType()));
					}
				}

				int max = length < entries.length ? length : entries.length;
				for(; i < max; i++) {
					ReflectionEntry e = entries[i];
					if(!e.isAvailable()) {
						continue;
					}

					MessagePackObject obj = array[i];
					if(obj.isNil()) {
						// this is Optional field becaue i >= minimumArrayLength
						// Optional + nil => keep default value
					} else {
						e.convert(to, obj);
						//e.set(to, obj.convert(e.getType()));
					}
				}

				// latter entries are all Optional + nil => keep default value

				return to;

			} catch (MessageTypeException e) {
				throw e;
			} catch (Exception e) {
				throw new MessageTypeException(e);
			}
		}
		
	}


	@Override
	public Template buildTemplate(Class<?> targetClass, IFieldEntry[] entries) {
		
		ReflectionEntry[] refEntries = new ReflectionEntry[entries.length];
		for(int i = 0;i < entries.length;i++){
			BeansFieldEntry e = (BeansFieldEntry)entries[i];
			Class<?> type = e.getType();
			if(type.equals(boolean.class)) {
				refEntries[i] = new ReflectionEntry(e);
			} else if(type.equals(byte.class)) {
				refEntries[i] = new ReflectionEntry(e);
			} else if(type.equals(short.class)) {
				refEntries[i] = new ReflectionEntry(e);
			} else if(type.equals(int.class)) {
				refEntries[i] = new ReflectionEntry(e);
			} else if(type.equals(long.class)) {
				refEntries[i] = new ReflectionEntry(e);
			} else if(type.equals(float.class)) {
				refEntries[i] = new ReflectionEntry(e);
			} else if(type.equals(double.class)) {
				refEntries[i] = new ReflectionEntry(e);
			} else {
				Template tmpl = TemplateRegistry.lookup(e.getGenericType(), true);
				refEntries[i] = new ObjectFieldEntry(e, tmpl);
			}
		}
		
		
		return new BeansReflectionTemplate(targetClass,refEntries);
	}
	
	
}
