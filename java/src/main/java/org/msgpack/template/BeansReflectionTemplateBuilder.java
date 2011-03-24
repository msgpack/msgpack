package org.msgpack.template;

import java.io.IOException;

import org.msgpack.AbstractTemplate;
import org.msgpack.MessagePackObject;
import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Template;
import org.msgpack.Unpacker;
import org.msgpack.template.builder.CustomTemplateBuilder;

public class BeansReflectionTemplateBuilder extends CustomTemplateBuilder{

	IFieldEntryReader reader = new BeansFieldEntryReader();
	
	public BeansReflectionTemplateBuilder(){}

	@Override
	public IFieldEntryReader getFieldEntryReader(){
		return reader;
	}
	
	
	static class BeansReflectionTemplate extends AbstractTemplate{
		
		Class<?> targetClass;
		BeansFieldEntry[] entries = null;
		protected int minimumArrayLength;
		
		public BeansReflectionTemplate(
				Class<?> targetClass,
				BeansFieldEntry[] entries){
			this.targetClass = targetClass;
			this.entries = entries;
			this.minimumArrayLength = 0;
			for(int i=0; i < entries.length; i++) {
				BeansFieldEntry e = entries[i];
				if(e.isRequired() || e.isNullable()) {
					this.minimumArrayLength = i+1;
				}
			}
		}
		

		@Override
		public void pack(Packer pk, Object target) throws IOException {
			
			pk.packArray(entries.length);
			for(BeansFieldEntry e : entries){
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
					BeansFieldEntry e = entries[i];
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
							e.set(to, null);
						}
					} else {
						e.set(to, pac.unpack(e.getType()));
					}
				}

				int max = length < entries.length ? length : entries.length;
				for(; i < max; i++) {
					BeansFieldEntry e = entries[i];
					if(!e.isAvailable()) {
						pac.unpackObject();
						continue;
					}

					if(pac.tryUnpackNull()) {
						// this is Optional field becaue i >= minimumArrayLength
						// Optional + nil => keep default value
					} else {
						e.set(to, pac.unpack(e.getType()));
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
					BeansFieldEntry e = entries[i];
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
							e.set(to,null);
						}
					} else {
						e.set(to, from.convert(e.getType()));
					}
				}

				int max = length < entries.length ? length : entries.length;
				for(; i < max; i++) {
					BeansFieldEntry e = entries[i];
					if(!e.isAvailable()) {
						continue;
					}

					MessagePackObject obj = array[i];
					if(obj.isNil()) {
						// this is Optional field becaue i >= minimumArrayLength
						// Optional + nil => keep default value
					} else {
						e.set(to, obj.convert(e.getType()));
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
		
		return new BeansReflectionTemplate(targetClass,(BeansFieldEntry[])entries);
	}
	
	
}
