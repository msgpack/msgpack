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
package org.msgpack;

import java.lang.Iterable;
import java.io.InputStream;
import java.io.IOException;
import java.util.Iterator;
import org.msgpack.impl.UnpackerImpl;

public class UnbufferedUnpacker extends UnpackerImpl {
	private int offset;
	private boolean finished;
	private Object data;

	public UnbufferedUnpacker() {
		super();
		this.offset = 0;
		this.finished = false;
	}

	public UnbufferedUnpacker useSchema(Schema s) {
		super.setSchema(s);
		return this;
	}

	public Object getData() {
		return data;
	}

	public boolean isFinished() {
		return finished;
	}

	public void reset() {
		super.reset();
		this.offset = 0;
	}

	int getOffset() {
		return offset;
	}

	void setOffset(int offset) {
		this.offset = offset;
	}

	public int execute(byte[] buffer) throws UnpackException {
		return execute(buffer, 0, buffer.length);
	}

	// FIXME
	public int execute(byte[] buffer, int offset, int length) throws UnpackException
	{
		int noffset = super.execute(buffer, offset + this.offset, length);
		this.offset = noffset - offset;
		if(super.isFinished()) {
			this.data = super.getData();
			this.finished = true;
			super.reset();
		} else {
			this.finished = false;
		}
		return noffset;
	}
}

