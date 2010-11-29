//
// MessagePack-RPC for Java
//
// Copyright (C) 2010 FURUHASHI Sadayuki
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
package org.msgpack.buffer;

import java.io.*;
import java.util.*;
import java.nio.*;
import java.nio.channels.*;
import org.msgpack.*;

public class VectoredByteBuffer implements GatheringByteChannel, ScatteringByteChannel {
	private List<ByteBuffer> vec = new ArrayList<ByteBuffer>();
	private ByteBuffer internalBuffer;
	private ByteBuffer lastInternalBuffer;
	private int bufferAllocSize;
	private int referenceThreshold = 32;

	public VectoredByteBuffer() {
		this(32*1024);
	}

	public VectoredByteBuffer(int size) {
		this.bufferAllocSize = size;
		internalBuffer = ByteBuffer.allocateDirect(size);
	}


	public synchronized void close() {
		vec.clear();
		lastInternalBuffer = null;
	}

	public boolean isOpen() {
		return true;  // FIXME?
	}


	public void write(int b) throws IOException {
		byte[] ba = new byte[1];
		ba[0] = (byte)b;
		write(ba);
	}

	public void write(byte[] b) throws IOException {
		write(b, 0, b.length);
	}

	public void write(byte[] b, int off, int len) throws IOException {
		if(len > referenceThreshold) {
			writeReference(b, off, len);
		} else {
			writeCopy(b, off, len);
		}
	}

	public int write(ByteBuffer src) throws IOException {
		int slen = src.remaining();
		if(slen > referenceThreshold) {
			writeCopy(src);
		} else {
			writeReference(src);
		}
		return slen;
	}

	public synchronized long write(ByteBuffer[] srcs) throws IOException {
		return write(srcs, 0, srcs.length);
	}

	public synchronized long write(ByteBuffer[] srcs, int offset, int length) throws IOException {
		long total = 0;
		for(int i=offset; offset < length; offset++) {
			ByteBuffer src = srcs[i];
			total += write(src);
		}
		return total;
	}

	private synchronized void writeCopy(byte[] b, int off, int len) throws IOException {
		int ipos = internalBuffer.position();
		if(internalBuffer.capacity() - ipos < len) {
			// allocate new buffer
			int nsize = bufferAllocSize > len ? bufferAllocSize : len;
			internalBuffer = ByteBuffer.allocateDirect(nsize);
			ipos = 0;
		} else if(internalBuffer == lastInternalBuffer) {
			ByteBuffer dup = vec.get(vec.size()-1);
			int dpos = dup.position();
			internalBuffer.put(b, off, len);
			ByteBuffer dup2 = internalBuffer.duplicate();
			dup2.position(dpos);
			dup2.limit(ipos + len);
			vec.set(vec.size()-1, dup2);
			return;
		}
		internalBuffer.put(b, off, len);
		ByteBuffer dup = internalBuffer.duplicate();
		dup.position(ipos);
		dup.mark();
		dup.limit(ipos + len);
		vec.add(dup);
		lastInternalBuffer = internalBuffer;
	}

	private synchronized void writeCopy(ByteBuffer src) throws IOException {
		int slen = src.remaining();
		int ipos = internalBuffer.position();
		if(internalBuffer.capacity() - ipos < slen) {
			// allocate new buffer
			int nsize = bufferAllocSize > slen ? bufferAllocSize : slen;
			internalBuffer = ByteBuffer.allocateDirect(nsize);
			ipos = 0;
		} else if(internalBuffer == lastInternalBuffer) {
			ByteBuffer dup = vec.get(vec.size()-1);
			int dpos = dup.position();
			internalBuffer.put(src);
			ByteBuffer dup2 = internalBuffer.duplicate();
			dup2.position(dpos);
			dup2.limit(ipos + slen);
			vec.set(vec.size()-1, dup2);
			return;
		}
		internalBuffer.put(src);
		ByteBuffer dup = internalBuffer.duplicate();
		dup.position(ipos);
		dup.mark();
		dup.limit(ipos + slen);
		vec.add(dup);
		lastInternalBuffer = internalBuffer;
	}

	private synchronized void writeReference(byte[] b, int off, int len) throws IOException {
		ByteBuffer buf = ByteBuffer.wrap(b, off, len);
		vec.add(buf);
		lastInternalBuffer = null;
	}

	private synchronized void writeReference(ByteBuffer src) throws IOException {
		ByteBuffer buf = src.duplicate();
		vec.add(buf);
		lastInternalBuffer = null;
	}

	public synchronized void writeTo(java.io.OutputStream out) throws IOException {
		byte[] tmpbuf = null;
		for(int i=0; i < vec.size(); i++) {
			ByteBuffer r = vec.get(i);
			int rpos = r.position();
			int rlen = r.limit() - rpos;
			if(r.hasArray()) {
				byte[] array = r.array();
				out.write(array, rpos, rlen);
			} else {
				if(tmpbuf == null) {
					int max = rlen;
					for(int j=i+1; j < vec.size(); j++) {
						ByteBuffer c = vec.get(j);
						int clen = c.remaining();
						if(max < clen) {
							max = clen;
						}
					}
					tmpbuf = new byte[max];
				}
				r.get(tmpbuf, 0, rlen);
				r.position(rpos);
				out.write(tmpbuf, 0, rlen);
			}
		}
	}

	public synchronized byte[] toByteArray() {
		byte[] out = new byte[available()];
		int off = 0;
		for(ByteBuffer r: vec) {
			int rpos = r.position();
			int rlen = r.limit() - rpos;
			r.get(out, off, rlen);
			r.position(rpos);
			off += rlen;
		}
		return out;
	}


	public synchronized int available() {
		int total = 0;
		for(ByteBuffer r : vec) {
			total += r.remaining();
		}
		return total;
	}

	public boolean markSupported () {
		return false;
	}

	public synchronized int read() {
		byte[] ba = new byte[1];
		if(read(ba) >= 1) {
			return ba[0];
		} else {
			return -1;
		}
	}

	public synchronized int read(byte[] b) {
		return read(b, 0, b.length);
	}

	public synchronized int read(byte[] b, int off, int len) {
		// FIXME check arguments
		int start = len;
		while(!vec.isEmpty()) {
			ByteBuffer r = vec.get(0);
			int rlen = r.remaining();
			if(rlen <= len) {
				r.get(b, off, rlen);
				vec.remove(0);
				off += rlen;
				len -= rlen;
			} else {
				r.get(b, off, len);
				return start;
			}
		}
		return start - len;
	}

	public synchronized int read(ByteBuffer dst) {
		int len = dst.remaining();
		int start = len;
		while(!vec.isEmpty()) {
			ByteBuffer r = vec.get(0);
			int rlen = r.remaining();
			if(rlen <= len) {
				dst.put(r);
				vec.remove(0);
				len -= rlen;
			} else {
				int blim = r.limit();
				r.limit(len);
				try {
					dst.put(r);
				} finally {
					r.limit(blim);
				}
				return start;
			}
		}
		return start - len;
	}

	public synchronized long read(ByteBuffer[] dsts) {
		return read(dsts, 0, dsts.length);
	}

	public synchronized long read(ByteBuffer[] dsts, int offset, int length) {
		long total = 0;
		for(int i=offset; i < length; i++) {
			ByteBuffer dst = dsts[i];
			int dlen = dst.remaining();
			int rlen = read(dsts[i]);
			total += rlen;
			if(rlen < dlen) {
				return total;
			}
		}
		return total;
	}

	public synchronized long read(GatheringByteChannel to) throws IOException {
		long total = to.write((ByteBuffer[])vec.toArray());
		while(!vec.isEmpty()) {
			ByteBuffer r = vec.get(0);
			if(r.remaining() == 0) {
				vec.remove(0);
			} else {
				break;
			}
		}
		return total;
	}

	public synchronized long skip(long len) {
		long start = len;
		while(!vec.isEmpty()) {
			ByteBuffer r = vec.get(0);
			int rlen = r.remaining();
			if(rlen <= len) {
				r.position(r.position()+rlen);
				vec.remove(0);
				len -= rlen;
			} else {
				r.position((int)(r.position()+len));
				return start;
			}
		}
		return start - len;
	}


	private final static class OutputStream extends java.io.OutputStream {
		private VectoredByteBuffer vbb;

		OutputStream(VectoredByteBuffer vbb) {
			this.vbb = vbb;
		}

		public void write(byte[] b) throws IOException {
			vbb.write(b);
		}

		public void write(byte[] b, int off, int len) throws IOException {
			vbb.write(b, off, len);
		}

		public void write(int b) throws IOException {
			vbb.write(b);
		}
	}


	private final static class InputStream extends java.io.InputStream {
		private VectoredByteBuffer vbb;

		InputStream(VectoredByteBuffer vbb) {
			this.vbb = vbb;
		}

		public int available() throws IOException {
			return vbb.available();
		}

		public int read(byte[] b) throws IOException {
			return vbb.read(b);
		}

		public int read(byte[] b, int off, int len) throws IOException {
			return vbb.read(b, off, len);
		}

		public int read() throws IOException {
			return vbb.read();
		}
	}


	public java.io.OutputStream outputStream() {
		return new OutputStream(this);
	}

	public java.io.InputStream inputStream() {
		return new InputStream(this);
	}
}

