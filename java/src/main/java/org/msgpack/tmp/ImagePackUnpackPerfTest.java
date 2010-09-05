package org.msgpack.tmp;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;

import org.msgpack.Packer;
import org.msgpack.Unpacker;

public class ImagePackUnpackPerfTest {

	private static int BIG_LOOP = 5;

	private static int SMALL_LOOP = 50000;

	private static DynamicCodeGenerator gen;

	private static void doGc() {
		try {
			Thread.sleep(50L);
		} catch (InterruptedException ie) {
			System.err
					.println("Interrupted while sleeping in serializers.BenchmarkRunner.doGc()");
		}
		System.gc();
		try { // longer sleep afterwards (not needed by GC, but may help with
			// scheduling)
			Thread.sleep(200L);
		} catch (InterruptedException ie) {
			System.err
					.println("Interrupted while sleeping in serializers.BenchmarkRunner.doGc()");
		}
	}

	public void doIt(int versionID) {
		try {
			doIt0(versionID);
		} catch (Exception e) {
			e.printStackTrace();
		}
		try {
			for (int j = 0; j < BIG_LOOP; ++j) {
				long t = System.currentTimeMillis();
				doIt0(versionID);
				t = System.currentTimeMillis() - t;
				System.out.println("time: " + t);
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void doIt0(int versionID) throws Exception {
		for (int i = 0; i < SMALL_LOOP; ++i) {
			switch (versionID) {
			case 0:
				doCurrentVersion();
				break;
			case 1:
				doWithReflection();
				break;
			case 2:
				doWithDynamicCodeGeneration();
				break;
			default:
				throw new RuntimeException();
			}
		}
	}

	public void doCurrentVersion() throws Exception {
		Image1 src = new Image1();
		src.title = "msgpack";
		src.uri = "http://msgpack.org/";
		src.width = 2560;
		src.height = 1600;
		src.size = 4096000;

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		src.messagePack(new Packer(out));
		Image1 dst = new Image1();
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		dst.messageUnpack(pac);
	}

	public void doWithReflection() throws Exception {
		Image2 src = new Image2();
		src.title = "msgpack";
		src.uri = "http://msgpack.org/";
		src.width = 2560;
		src.height = 1600;
		src.size = 4096000;

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		src.messagePack(new Packer(out));
		Image2 dst = new Image2();
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		dst.messageUnpack(pac);
	}

	public void doWithDynamicCodeGeneration() throws Exception {
		Image3 src = (Image3) gen.newEnhancedInstance(Image3.class);
		src.title = "msgpack";
		src.uri = "http://msgpack.org/";
		src.width = 2560;
		src.height = 1600;
		src.size = 4096000;

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		src.messagePack(new Packer(out));
		Image3 dst = (Image3) gen.newEnhancedInstance(Image3.class);
		ByteArrayInputStream in = new ByteArrayInputStream(out.toByteArray());
		Unpacker pac = new Unpacker(in);
		dst.messageUnpack(pac);
	}

	public static void main(String[] args) {
		ImagePackUnpackPerfTest test = new ImagePackUnpackPerfTest();

		doGc();
		System.out.println("test current version");
		test.doIt(0);

		doGc();
		System.out.println("test with reflection");
		test.doIt(1);

		doGc();
		System.out.println("test with dynamic codegen");
		gen = new DynamicCodeGenerator();
		test.doIt(2);
	}
}
