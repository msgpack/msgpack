//
// MessagePack for Java
//
// Copyright (C) 2009-2010 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
package org.msgpack.type;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import org.msgpack.*;

public final class Raw {
	private byte[] bytes;
	private String string;

	public Raw(byte[] bytes) {
		this.bytes = bytes;
		this.string = null;
	}

	public Raw(String string) {
		this.bytes = null;
		this.string = string;
	}

	public String toString() {
		if(string == null) {
			try {
				string = new String(bytes, "UTF-8");
			} catch (UnsupportedEncodingException e) {
				throw new RuntimeException(e);
			}
		}
		return string;
	}

	public byte[] toByteArray() {
		if(bytes == null) {
			try {
				bytes = string.getBytes("UTF-8");
			} catch (UnsupportedEncodingException e) {
				throw new RuntimeException(e);
			}
		}
		return bytes;
	}

	public ByteBuffer toByteBuffer() {
		return ByteBuffer.wrap(toByteArray());
	}

	static {
		RawTemplate.load();
	}
}

