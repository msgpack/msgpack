package serializers.msgpack;

import java.util.*;
import java.io.*;
import org.msgpack.*;
import org.msgpack.schema.*;

public final class MediaContent implements MessagePackable, MessageConvertable, MessageMergeable
{
	private static final ClassSchema _SCHEMA = (ClassSchema)Schema.load("(class MediaContent (package serializers.msgpack) (field image (array (class Image (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field size int)))) (field media (class Media (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field format string) (field duration long) (field size long) (field bitrate int) (field person (array string)) (field player int) (field copyright string))))");
	public static ClassSchema getSchema() { return _SCHEMA; }

	public ArrayList<Image> image;
	public Media media;

	public MediaContent() { }

	@Override
	public void messagePack(Packer pk) throws IOException
	{
		List<? extends FieldSchema> _f = _SCHEMA.getFields();
		pk.packArray(2);
		_f.get(0).getType().pack(pk, image);
		_f.get(1).getType().pack(pk, media);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void messageConvert(GenericObject obj)
	{
		List<GenericObject> _l = obj.asArray();
		List<? extends FieldSchema> _f = _SCHEMA.getFields();
		if(_l.size() <= 0) { return; } image = (ArrayList<Image>)_f.get(0).getType().convert(_l.get(0));
		if(_l.size() <= 1) { return; } media = (Media)_f.get(1).getType().convert(_l.get(1));
	}

	public static MediaContent convert(GenericObject obj)
	{
		return (MediaContent)_SCHEMA.convert(obj);
	}

	public void setField(int index, Object value)
	{
		switch(index) {
		case 0:
			image = (ArrayList<Image>)value;
			break;
		case 1:
			media = (Media)value;
			break;
		}
	}

	public Object getField(int index)
	{
		switch(index) {
		case 0:
			return image;
		case 1:
			return media;
		}
		return null;
	}
}

final class Image implements MessagePackable, MessageConvertable, MessageMergeable
{
	private static final ClassSchema _SCHEMA = (ClassSchema)Schema.load("(class Image (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field size int))");
	public static ClassSchema getSchema() { return _SCHEMA; }

	public String uri;
	public String title;
	public Integer width;
	public Integer height;
	public Integer size;

	public Image() { }

	@Override
	public void messagePack(Packer pk) throws IOException
	{
		List<? extends FieldSchema> _f = _SCHEMA.getFields();
		pk.packArray(5);
		_f.get(0).getType().pack(pk, uri);
		_f.get(1).getType().pack(pk, title);
		_f.get(2).getType().pack(pk, width);
		_f.get(3).getType().pack(pk, height);
		_f.get(4).getType().pack(pk, size);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void messageConvert(GenericObject obj)
	{
		List<GenericObject> _l = obj.asArray();
		List<? extends FieldSchema> _f = _SCHEMA.getFields();
		if(_l.size() <= 0) { return; } uri = (String)_f.get(0).getType().convert(_l.get(0));
		if(_l.size() <= 1) { return; } title = (String)_f.get(1).getType().convert(_l.get(1));
		if(_l.size() <= 2) { return; } width = (Integer)_f.get(2).getType().convert(_l.get(2));
		if(_l.size() <= 3) { return; } height = (Integer)_f.get(3).getType().convert(_l.get(3));
		if(_l.size() <= 4) { return; } size = (Integer)_f.get(4).getType().convert(_l.get(4));
	}

	public static Image convert(GenericObject obj)
	{
		return (Image)_SCHEMA.convert(obj);
	}

	public void setField(int index, Object value)
	{
		switch(index) {
		case 0:
			uri = (String)value;
			break;
		case 1:
			title = (String)value;
			break;
		case 2:
			width = (Integer)value;
			break;
		case 3:
			height = (Integer)value;
			break;
		case 4:
			size = (Integer)value;
			break;
		}
	}

	public Object getField(int index)
	{
		switch(index) {
		case 0:
			return uri;
		case 1:
			return title;
		case 2:
			return width;
		case 3:
			return height;
		case 4:
			return size;
		}
		return null;
	}
}

final class Media implements MessagePackable, MessageConvertable, MessageMergeable
{
	private static final ClassSchema _SCHEMA = (ClassSchema)Schema.load("(class Media (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field format string) (field duration long) (field size long) (field bitrate int) (field person (array string)) (field player int) (field copyright string))");
	public static ClassSchema getSchema() { return _SCHEMA; }

	public String uri;
	public String title;
	public Integer width;
	public Integer height;
	public String format;
	public Long duration;
	public Long size;
	public Integer bitrate;
	public ArrayList<String> person;
	public Integer player;
	public String copyright;

	public Media() { }

	@Override
	public void messagePack(Packer pk) throws IOException
	{
		List<? extends FieldSchema> _f = _SCHEMA.getFields();
		pk.packArray(11);
		_f.get(0).getType().pack(pk, uri);
		_f.get(1).getType().pack(pk, title);
		_f.get(2).getType().pack(pk, width);
		_f.get(3).getType().pack(pk, height);
		_f.get(4).getType().pack(pk, format);
		_f.get(5).getType().pack(pk, duration);
		_f.get(6).getType().pack(pk, size);
		_f.get(7).getType().pack(pk, bitrate);
		_f.get(8).getType().pack(pk, person);
		_f.get(9).getType().pack(pk, player);
		_f.get(10).getType().pack(pk, copyright);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void messageConvert(GenericObject obj)
	{
		List<GenericObject> _l = obj.asArray();
		List<? extends FieldSchema> _f = _SCHEMA.getFields();
		if(_l.size() <= 0) { return; } uri = (String)_f.get(0).getType().convert(_l.get(0));
		if(_l.size() <= 1) { return; } title = (String)_f.get(1).getType().convert(_l.get(1));
		if(_l.size() <= 2) { return; } width = (Integer)_f.get(2).getType().convert(_l.get(2));
		if(_l.size() <= 3) { return; } height = (Integer)_f.get(3).getType().convert(_l.get(3));
		if(_l.size() <= 4) { return; } format = (String)_f.get(4).getType().convert(_l.get(4));
		if(_l.size() <= 5) { return; } duration = (Long)_f.get(5).getType().convert(_l.get(5));
		if(_l.size() <= 6) { return; } size = (Long)_f.get(6).getType().convert(_l.get(6));
		if(_l.size() <= 7) { return; } bitrate = (Integer)_f.get(7).getType().convert(_l.get(7));
		if(_l.size() <= 8) { return; } person = (ArrayList<String>)_f.get(8).getType().convert(_l.get(8));
		if(_l.size() <= 9) { return; } player = (Integer)_f.get(9).getType().convert(_l.get(9));
		if(_l.size() <= 10) { return; } copyright = (String)_f.get(10).getType().convert(_l.get(10));
	}

	public static Media convert(GenericObject obj)
	{
		return (Media)_SCHEMA.convert(obj);
	}

	public void setField(int index, Object value)
	{
		switch(index) {
		case 0:
			uri = (String)value;
			break;
		case 1:
			title = (String)value;
			break;
		case 2:
			width = (Integer)value;
			break;
		case 3:
			height = (Integer)value;
			break;
		case 4:
			format = (String)value;
			break;
		case 5:
			duration = (Long)value;
			break;
		case 6:
			size = (Long)value;
			break;
		case 7:
			bitrate = (Integer)value;
			break;
		case 8:
			person = (ArrayList<String>)value;
			break;
		case 9:
			player = (Integer)value;
			break;
		case 10:
			copyright = (String)value;
			break;
		}
	}

	public Object getField(int index)
	{
		switch(index) {
		case 0:
			return uri;
		case 1:
			return title;
		case 2:
			return width;
		case 3:
			return height;
		case 4:
			return format;
		case 5:
			return duration;
		case 6:
			return size;
		case 7:
			return bitrate;
		case 8:
			return person;
		case 9:
			return player;
		case 10:
			return copyright;
		}
		return null;
	}

}
