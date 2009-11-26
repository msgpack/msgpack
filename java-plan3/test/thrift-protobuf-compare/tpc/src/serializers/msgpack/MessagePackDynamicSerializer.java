package serializers.msgpack;

import java.io.*;
import java.util.*;
import org.msgpack.*;
import serializers.ObjectSerializer;

public class MessagePackDynamicSerializer implements ObjectSerializer<Object>
{
	public String getName() {
		return "msgpack-dynamic";
	}

	public Object create() throws Exception {
		ArrayList media = new ArrayList(11);
		media.add("http://javaone.com/keynote.mpg");
		media.add("video/mpg4");
		media.add("Javaone Keynote");
		media.add(1234567L);
		media.add(0);
		ArrayList<String> person = new ArrayList<String>(2);
		person.add("Bill Gates");
		person.add("Steve Jobs");
		media.add(person);
		media.add(0);
		media.add(0);
		media.add(0);
		media.add(123L);
		media.add("");

		ArrayList image1 = new ArrayList(5);
		image1.add("http://javaone.com/keynote_large.jpg");
		image1.add(0);
		image1.add(0);
		image1.add(2);
		image1.add("Javaone Keynote");

		ArrayList image2 = new ArrayList(5);
		image2.add("http://javaone.com/keynote_thumbnail.jpg");
		image2.add(0);
		image2.add(0);
		image2.add(1);
		image2.add("Javaone Keynote");

		ArrayList content = new ArrayList(2);
		content.add(media);
		ArrayList<Object> images = new ArrayList<Object>(2);
		images.add(image1);
		images.add(image2);
		content.add(images);

		return content;
	}

	public byte[] serialize(Object content) throws Exception {
		ByteArrayOutputStream os = new ByteArrayOutputStream();
		Packer pk = new Packer(os);
		pk.pack(content);
		return os.toByteArray();
	}

	public Object deserialize(byte[] array) throws Exception {
		UnbufferedUnpacker pac = new UnbufferedUnpacker();
		pac.execute(array);
		return (Object)pac.getData();
	}
}

