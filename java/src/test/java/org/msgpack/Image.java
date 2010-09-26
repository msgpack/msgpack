package org.msgpack;

import org.msgpack.*;
import java.io.*;
import java.util.*;

public class Image implements MessagePackable, MessageUnpackable {
	public String uri = "";
	public String title = "";
	public int width = 0;
	public int height = 0;
	public int size = 0;

	public void messagePack(Packer pk) throws IOException {
		pk.packArray(5);
		pk.pack(uri);
		pk.pack(title);
		pk.pack(width);
		pk.pack(height);
		pk.pack(size);
	}

	public void messageUnpack(Unpacker pac) throws IOException, MessageTypeException {
		int length = pac.unpackArray();
		if(length != 5) {
			throw new MessageTypeException();
		}
		uri = pac.unpackString();
		title = pac.unpackString();
		width = pac.unpackInt();
		height = pac.unpackInt();
		size = pac.unpackInt();
	}

	public boolean equals(Image obj) {
		return uri.equals(obj.uri) &&
			title.equals(obj.title) &&
			width == obj.width &&
			height == obj.height &&
			size == obj.size;
	}

	public boolean equals(Object obj) {
		if(obj.getClass() != Image.class) {
			return false;
		}
		return equals((Image)obj);
	}
}

