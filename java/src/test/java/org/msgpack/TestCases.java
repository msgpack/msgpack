package org.msgpack;

import java.io.*;
import java.util.*;

import org.junit.Test;
import static org.junit.Assert.*;

public class TestCases {
	public void feedFile(Unpacker pac, String path) throws Exception {
		FileInputStream input = new FileInputStream(path);
		byte[] buffer = new byte[32*1024];
		while(true) {
			int count = input.read(buffer);
			if(count < 0) {
				break;
			}
			pac.feed(buffer, 0, count);
		}
	}

	@Test
	public void testCases() throws Exception {
		Unpacker pac = new Unpacker();
		Unpacker pac_compact = new Unpacker();

		feedFile(pac, "src/test/resources/cases.mpac");
		feedFile(pac_compact, "src/test/resources/cases_compact.mpac");

		UnpackResult result = new UnpackResult();
		while(pac.next(result)) {
			UnpackResult result_compact = new UnpackResult();
			assertTrue( pac_compact.next(result_compact) );
			assertTrue( result.getData().equals(result_compact.getData()) );
		}

		assertFalse( pac_compact.next(result) );
	}
};

