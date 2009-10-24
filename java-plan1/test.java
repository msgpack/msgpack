import java.util.*;
import java.io.*;

class OpenByteArrayOutputStream extends ByteArrayOutputStream {
	int getCount() { return count; }
	byte[] getBuffer() { return buf; }
}


public class test {

	public static void main(String[] args) throws IOException
	{
		testSimple();
		testStreaming();
	}


	public static void testSimple() throws IOException
	{
		OpenByteArrayOutputStream out = new OpenByteArrayOutputStream();

		Packer pk = new Packer(out);
		pk.packArray(3)
			.packInt(1)
			.packByte((byte)2)
			.packDouble(0.3);

		Unpacker pac = new Unpacker();
		int nlen = pac.execute(out.getBuffer(), 0, out.getCount());

		if(pac.isFinished()) {
			System.out.println("testSimple: "+pac.getData());
		}
	}


	public static void testStreaming() throws IOException
	{
		OpenByteArrayOutputStream out = new OpenByteArrayOutputStream();

		////
		// sender
		//
		// initialize the streaming serializer
		Packer pk = new Packer(out);

		// serialize 2 objects
		pk.packArray(3)
			.packInt(0)
			.packByte((byte)1)
			.packDouble(0.2);
		pk.packArray(3)
			.packInt(3)
			.packByte((byte)4)
			.packDouble(0.5);

		// send it through the network
		InputStream sock = new ByteArrayInputStream(out.getBuffer(), 0, out.getCount());


		////
		// receiver
		//
		// initialize the streaming deserializer
		Unpacker pac = new Unpacker();
		int parsed = 0;

		byte[] buf = new byte[1024];
		int buflen = 0;

		while(true) {
			// receive data from the network
			int c = sock.read();
			if(c < 0) { return; }

			buf[buflen++] = (byte)c;

			// deserialize
			parsed = pac.execute(buf, parsed, buflen);
			if(pac.isFinished()) {
				// get an object
				Object msg = pac.getData();
				System.out.println("testStreaming: "+msg);

				// reset the streaming deserializer
				pac.reset();
				buflen = 0;
				parsed = 0;
			}
		}
	}
}

