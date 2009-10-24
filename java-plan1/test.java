import java.util.*;
import java.io.*;

class OpenByteArrayOutputStream extends ByteArrayOutputStream {
	int getCount() { return count; }
	byte[] getBuffer() { return buf; }
}

public class test {
	public static void main(String[] args) throws IOException
	{
		OpenByteArrayOutputStream out = new OpenByteArrayOutputStream();

		Packer pk = new Packer(out);
		pk.packArray(3)
			.packInt(0)
			.packByte((byte)1)
			.packDouble(0.1);

		Unpacker pac = new Unpacker();
		int nlen = pac.execute(out.getBuffer(), 0, out.getCount());
		if(pac.isFinished()) {
			System.out.println(pac.getData());
		}
	}
}

