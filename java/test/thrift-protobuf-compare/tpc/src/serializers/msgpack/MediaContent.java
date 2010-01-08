package serializers.msgpack;

import java.util.*;
import java.io.*;
import org.msgpack.*;
import org.msgpack.schema.ClassSchema;
import org.msgpack.schema.FieldSchema;

public final class MediaContent implements MessagePackable, MessageMergeable
{
	private static final ClassSchema _SCHEMA = (ClassSchema)Schema.load("(class MediaContent (package serializers.msgpack) (field image (array (class Image (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field size int)))) (field media (class Media (package serializers.msgpack) (field uri string) (field title string) (field width int) (field height int) (field format string) (field duration long) (field size long) (field bitrate int) (field person (array string)) (field player int) (field copyright string))))");
	public static ClassSchema getSchema() { return _SCHEMA; }

	public List<Image> image;
	public Media media;

	public MediaContent() { }

	@Override
	public void messagePack(Packer _pk) throws IOException
	{
		_pk.packArray(2);
		FieldSchema[] _fields = _SCHEMA.getFields();
		_fields[0].getSchema().pack(_pk, image);
		_fields[1].getSchema().pack(_pk, media);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void messageMerge(Object obj) throws MessageTypeException
	{
		Object[] _source = ((List)obj).toArray();
		FieldSchema[] _fields = _SCHEMA.getFields();
		if(_source.length <= 0) { return; } this.image = (List<Image>)_fields[0].getSchema().convert(_source[0]);
		if(_source.length <= 1) { return; } this.media = (Media)_fields[1].getSchema().convert(_source[1]);
	}

	@SuppressWarnings("unchecked")
	public static MediaContent createFromMessage(Object[] _message)
	{
		MediaContent _self = new MediaContent();
		if(_message.length <= 0) { return _self; } _self.image = (List<Image>)_message[0];
		if(_message.length <= 1) { return _self; } _self.media = (Media)_message[1];
		return _self;
	}
}

final class Image implements MessagePackable, MessageMergeable
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
	public void messagePack(Packer _pk) throws IOException
	{
		_pk.packArray(5);
		FieldSchema[] _fields = _SCHEMA.getFields();
		_fields[0].getSchema().pack(_pk, uri);
		_fields[1].getSchema().pack(_pk, title);
		_fields[2].getSchema().pack(_pk, width);
		_fields[3].getSchema().pack(_pk, height);
		_fields[4].getSchema().pack(_pk, size);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void messageMerge(Object obj) throws MessageTypeException
	{
		Object[] _source = ((List)obj).toArray();
		FieldSchema[] _fields = _SCHEMA.getFields();
		if(_source.length <= 0) { return; } this.uri = (String)_fields[0].getSchema().convert(_source[0]);
		if(_source.length <= 1) { return; } this.title = (String)_fields[1].getSchema().convert(_source[1]);
		if(_source.length <= 2) { return; } this.width = (Integer)_fields[2].getSchema().convert(_source[2]);
		if(_source.length <= 3) { return; } this.height = (Integer)_fields[3].getSchema().convert(_source[3]);
		if(_source.length <= 4) { return; } this.size = (Integer)_fields[4].getSchema().convert(_source[4]);
	}

	@SuppressWarnings("unchecked")
	public static Image createFromMessage(Object[] _message)
	{
		Image _self = new Image();
		if(_message.length <= 0) { return _self; } _self.uri = (String)_message[0];
		if(_message.length <= 1) { return _self; } _self.title = (String)_message[1];
		if(_message.length <= 2) { return _self; } _self.width = (Integer)_message[2];
		if(_message.length <= 3) { return _self; } _self.height = (Integer)_message[3];
		if(_message.length <= 4) { return _self; } _self.size = (Integer)_message[4];
		return _self;
	}
}

final class Media implements MessagePackable, MessageMergeable
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
	public List<String> person;
	public Integer player;
	public String copyright;

	public Media() { }

	@Override
	public void messagePack(Packer _pk) throws IOException
	{
		_pk.packArray(11);
		FieldSchema[] _fields = _SCHEMA.getFields();
		_fields[0].getSchema().pack(_pk, uri);
		_fields[1].getSchema().pack(_pk, title);
		_fields[2].getSchema().pack(_pk, width);
		_fields[3].getSchema().pack(_pk, height);
		_fields[4].getSchema().pack(_pk, format);
		_fields[5].getSchema().pack(_pk, duration);
		_fields[6].getSchema().pack(_pk, size);
		_fields[7].getSchema().pack(_pk, bitrate);
		_fields[8].getSchema().pack(_pk, person);
		_fields[9].getSchema().pack(_pk, player);
		_fields[10].getSchema().pack(_pk, copyright);
	}

	@Override
	@SuppressWarnings("unchecked")
	public void messageMerge(Object obj) throws MessageTypeException
	{
		Object[] _source = ((List)obj).toArray();
		FieldSchema[] _fields = _SCHEMA.getFields();
		if(_source.length <= 0) { return; } this.uri = (String)_fields[0].getSchema().convert(_source[0]);
		if(_source.length <= 1) { return; } this.title = (String)_fields[1].getSchema().convert(_source[1]);
		if(_source.length <= 2) { return; } this.width = (Integer)_fields[2].getSchema().convert(_source[2]);
		if(_source.length <= 3) { return; } this.height = (Integer)_fields[3].getSchema().convert(_source[3]);
		if(_source.length <= 4) { return; } this.format = (String)_fields[4].getSchema().convert(_source[4]);
		if(_source.length <= 5) { return; } this.duration = (Long)_fields[5].getSchema().convert(_source[5]);
		if(_source.length <= 6) { return; } this.size = (Long)_fields[6].getSchema().convert(_source[6]);
		if(_source.length <= 7) { return; } this.bitrate = (Integer)_fields[7].getSchema().convert(_source[7]);
		if(_source.length <= 8) { return; } this.person = (List<String>)_fields[8].getSchema().convert(_source[8]);
		if(_source.length <= 9) { return; } this.player = (Integer)_fields[9].getSchema().convert(_source[9]);
		if(_source.length <= 10) { return; } this.copyright = (String)_fields[10].getSchema().convert(_source[10]);
	}

	@SuppressWarnings("unchecked")
	public static Media createFromMessage(Object[] _message)
	{
		Media _self = new Media();
		if(_message.length <= 0) { return _self; } _self.uri = (String)_message[0];
		if(_message.length <= 1) { return _self; } _self.title = (String)_message[1];
		if(_message.length <= 2) { return _self; } _self.width = (Integer)_message[2];
		if(_message.length <= 3) { return _self; } _self.height = (Integer)_message[3];
		if(_message.length <= 4) { return _self; } _self.format = (String)_message[4];
		if(_message.length <= 5) { return _self; } _self.duration = (Long)_message[5];
		if(_message.length <= 6) { return _self; } _self.size = (Long)_message[6];
		if(_message.length <= 7) { return _self; } _self.bitrate = (Integer)_message[7];
		if(_message.length <= 8) { return _self; } _self.person = (List<String>)_message[8];
		if(_message.length <= 9) { return _self; } _self.player = (Integer)_message[9];
		if(_message.length <= 10) { return _self; } _self.copyright = (String)_message[10];
		return _self;
	}
}

