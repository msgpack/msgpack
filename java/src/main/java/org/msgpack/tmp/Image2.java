package org.msgpack.tmp;

import java.io.IOException;
import java.lang.reflect.Field;

import org.msgpack.MessageTypeException;
import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class Image2 {
	public String uri = "";
	public String title = "";
	public int width = 0;
	public int height = 0;
	public int size = 0;

	public void messagePack(Packer pk) throws IOException {
		messagePackWithReflection(pk);
	}

	public void messagePackWithReflection(Packer pk) throws IOException {
		Class<?> cl = this.getClass();
		Field[] fields = cl.getFields();
		pk.packArray(fields.length);
		for (Field field : fields) {
			try {
				Object obj = field.get(this);
				pk.pack(obj);
			} catch (IllegalArgumentException e) {
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				e.printStackTrace();
			}
		}
	}

	public void messageUnpack(Unpacker pac) throws IOException,
			MessageTypeException {
		messageUnpackWithReflection(pac);
	}
	
	public void messageUnpackWithReflection(Unpacker pac) throws IOException,
			MessageTypeException {
		Class<?> cl = this.getClass();
		Field[] fields = cl.getFields();
		int length = pac.unpackArray();
		if (length != fields.length) {
			throw new MessageTypeException();
		}
		for (Field field : fields) {
			try {
				field.set(this, unpack(pac, field.getType()));
			} catch (IOException e) {
				e.printStackTrace();
			} catch (IllegalArgumentException e) {
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				e.printStackTrace();
			}
		}
	}
	
	public static Object unpack(Unpacker pk, Class<?> cl) throws IOException {
		if (cl == int.class) {
			return pk.unpackInt();
		} else if (cl == String.class) {
			return pk.unpackString();
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public boolean equals(Image2 obj) {
		return uri.equals(obj.uri) && title.equals(obj.title)
				&& width == obj.width && height == obj.height
				&& size == obj.size;
	}

	public boolean equals(Object obj) {
		if (obj.getClass() != Image2.class) {
			return false;
		}
		return equals((Image2) obj);
	}
}
