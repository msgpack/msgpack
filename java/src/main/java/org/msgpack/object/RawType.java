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
package org.msgpack.object;

import java.util.Arrays;
import java.io.IOException;
import org.msgpack.*;

public class RawType extends MessagePackObject {
	private byte[] bytes;

	RawType(byte[] bytes) {
		this.bytes = bytes;
	}

	RawType(String str) {
		try {
			this.bytes = str.getBytes("UTF-8");
		} catch (Exception e) {
			throw new MessageTypeException("type error");
		}
	}

	public static RawType create(byte[] bytes) {
		return new RawType(bytes);
	}

	public static RawType create(String str) {
		return new RawType(str);
	}

	@Override
	public boolean isRawType() {
		return true;
	}

	@Override
	public byte[] asByteArray() {
		return bytes;
	}

	@Override
	public String asString() {
		try {
			return new String(bytes, "UTF-8");
		} catch (Exception e) {
			throw new MessageTypeException("type error");
		}
	}

	@Override
	public void messagePack(Packer pk) throws IOException {
		pk.packRaw(bytes.length);
		pk.packRawBody(bytes);
	}

	@Override
	public boolean equals(Object obj) {
		if(obj.getClass() != getClass()) {
			return false;
		}
		return Arrays.equals(((RawType)obj).bytes, bytes);
	}

	@Override
	public int hashCode() {
		return bytes.hashCode();
	}

	@Override
	public Object clone() {
		return new RawType((byte[])bytes.clone());
	}
}

