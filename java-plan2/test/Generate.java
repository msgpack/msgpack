import java.io.*;
import java.util.*;
import org.msgpack.*;
import org.msgpack.schema.*;

public class Generate {
	public static void main(String[] args) throws IOException
	{
		Writer output = new OutputStreamWriter(System.out);

		Schema s1 = Schema.parse("(class Test (field uri raw) (field width int))");
		ClassGenerator.write(s1, output);

		Schema s1 = Schema.parse("(class MediaContent (package serializers.msgpack) (field image (array (class Image (field uri string) (field title string) (field width int) (field height int) (field size int)))) (field media (class Media (field uri string) (field title string) (field width int) (field height int) (field format string) (field duration long) (field size long) (field bitrate int) (field person (array string)) (field player int) (field copyright string))))");
		ClassGenerator.write(s2, output);
	}
}

