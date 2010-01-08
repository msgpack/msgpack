package serializers.msgpack;

import java.io.*;
import java.util.*;
import org.msgpack.*;
import serializers.ObjectSerializer;

public class MessagePackGenericSerializer implements ObjectSerializer<Object>
{
	private static final Schema MEDIA_CONTENT_SCHEMA = Schema.parse("(class MediaContent (package serializers.msgpack) (field image (array (class Image (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field size int)))) (field media (class Media (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field format string) (field duration long) (field size long) (field bitrate int) (field person (array string)) (field player int) (field copyright string))))");

	public String getName() {
		return "msgpack-generic";
	}

	public Object create() throws Exception {
		HashMap<String,Object> media = new HashMap<String, Object>(11);
		media.put("uri", "http://javaone.com/keynote.mpg");
		media.put("format", "video/mpg4");
		media.put("title", "Javaone Keynote");
		media.put("duration", 1234567L);
		media.put("bitrate", 0);
		ArrayList<String> person = new ArrayList<String>(2);
		person.add("Bill Gates");
		person.add("Steve Jobs");
		media.put("person", person);
		media.put("player", 0);
		media.put("height", 0);
		media.put("width", 0);
		media.put("size", 123L);
		media.put("copyright", "");

		HashMap<String,Object> image1 = new HashMap<String,Object>(5);
		image1.put("uri", "http://javaone.com/keynote_large.jpg");
		image1.put("width", 0);
		image1.put("height", 0);
		image1.put("size", 2);
		image1.put("title", "Javaone Keynote");

		HashMap<String,Object> image2 = new HashMap<String,Object>(5);
		image2.put("uri", "http://javaone.com/keynote_thumbnail.jpg");
		image2.put("width", 0);
		image2.put("height", 0);
		image2.put("size", 1);
		image2.put("title", "Javaone Keynote");

		HashMap<String,Object> content = new HashMap<String,Object>(2);
		content.put("media", media);
		ArrayList<Object> images = new ArrayList<Object>(2);
		images.add(image1);
		images.add(image2);
		content.put("image", images);

		return content;
	}

	public byte[] serialize(Object content) throws Exception {
		ByteArrayOutputStream os = new ByteArrayOutputStream();
		Packer pk = new Packer(os);
		pk.packWithSchema(content, MEDIA_CONTENT_SCHEMA);
		return os.toByteArray();
	}

	public Object deserialize(byte[] array) throws Exception {
		UnbufferedUnpacker pac = new UnbufferedUnpacker().useSchema(MEDIA_CONTENT_SCHEMA);
		pac.execute(array);
		return (Object)pac.getData();
	}
}

