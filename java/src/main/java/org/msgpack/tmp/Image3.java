package org.msgpack.tmp;

import java.io.IOException;
import org.msgpack.MessagePackable;
import org.msgpack.MessageTypeException;
import org.msgpack.MessageUnpackable;
import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class Image3 implements MessagePackable, MessageUnpackable {
	public String uri = "";
	public String title = "";
	public int width = 0;
	public int height = 0;
	public int size = 0;

	public void messagePack(Packer pk) throws IOException {
		// empty
	}

	public void messageUnpack(Unpacker pac) throws IOException,
			MessageTypeException {
		// empty
	}

	public boolean equals(Image3 obj) {
		return uri.equals(obj.uri) && title.equals(obj.title)
				&& width == obj.width && height == obj.height
				&& size == obj.size;
	}

	public boolean equals(Object obj) {
		if (obj.getClass() != Image3.class) {
			return false;
		}
		return equals((Image3) obj);
	}
}