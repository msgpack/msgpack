package serializers.msgpack;

import java.io.*;
import java.util.*;
import org.msgpack.*;
import serializers.ObjectSerializer;

public class MessagePackIndirectSerializer implements ObjectSerializer<MediaContent>
{
	public String getName() {
		return "msgpack-indirect";
	}

	public MediaContent create() throws Exception {
		Media media = new Media();
		media.uri = "http://javaone.com/keynote.mpg";
		media.format = "video/mpg4";
		media.title = "Javaone Keynote";
		media.duration = 1234567L;
		media.bitrate = 0;
		media.person = new ArrayList<String>(2);
		media.person.add("Bill Gates");
		media.person.add("Steve Jobs");
		media.player = 0;
		media.height = 0;
		media.width = 0;
		media.size = 123L;
		media.copyright = "";

		Image image1 = new Image();
		image1.uri = "http://javaone.com/keynote_large.jpg";
		image1.width = 0;
		image1.height = 0;
		image1.size = 2;
		image1.title = "Javaone Keynote";

		Image image2 = new Image();
		image2.uri = "http://javaone.com/keynote_thumbnail.jpg";
		image2.width = 0;
		image2.height = 0;
		image2.size = 1;
		image2.title = "Javaone Keynote";

		MediaContent content = new MediaContent();
		content.media = media;
		content.image = new ArrayList<Image>(2);
		content.image.add(image1);
		content.image.add(image2);

		return content;
	}

	public byte[] serialize(MediaContent content) throws Exception {
		ByteArrayOutputStream os = new ByteArrayOutputStream();
		Packer pk = new Packer(os);
		pk.pack(content);
		return os.toByteArray();
	}

	public MediaContent deserialize(byte[] array) throws Exception {
		UnbufferedUnpacker pac = new UnbufferedUnpacker();
		pac.execute(array);
		Object obj = pac.getData();
		return (MediaContent)MediaContent.getSchema().convert(obj);
	}
}

