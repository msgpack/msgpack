//
// MessagePack for Java
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

import java.io.InputStream;
import java.io.OutputStream;
import java.io.IOException;
import java.util.List;
import java.util.ArrayList;
import java.nio.ByteBuffer;
import java.nio.channels.GatheringByteChannel;
import java.nio.channels.ScatteringByteChannel;

public class VectoredByteBuffer implements GatheringByteChannel, ScatteringByteChannel {
	private List<ByteBuffer> vec = new ArrayList<ByteBuffer>();
	private ByteBuffer internalBuffer;
	private ByteBuffer lastInternalBuffer;
	private int chunkSize;
	private int referenceThreshold;

	public VectoredByteBuffer() {
		this(32*1024);
	}

	public VectoredByteBuffer(int chunkSize) {
		this(chunkSize, 32);
	}

	public VectoredByteBuffer(int chunkSize, int referenceThreshold) {
		this.chunkSize = chunkSize;
		this.referenceThreshold = referenceThreshold;
		internalBuffer = ByteBuffer.allocateDirect(chunkSize);
	}


	public void setChunkSize(int chunkSize) {
		this.chunkSize = chunkSize;
	}

	public int getChunkSize(int chunkSize) {
		return this.chunkSize;
	}

	public void setReferenceThreshold(int referenceThreshold) {
		this.referenceThreshold = referenceThreshold;
	}

	public int getReferenceThreshold(int referenceThreshold) {
		return this.referenceThreshold;
	}


	@Override
	public void close() {
		reset();
	}

	@Override
	public boolean isOpen() {
		return true;  // FIXME?
	}


	public synchronized void reset() {
		vec.clear();
		lastInternalBuffer = null;
	}


	public void write(byte[] b) {
		write(b, 0, b.length);
	}

	public void write(byte[] b, int off, int len) {
		if(off < 0 || len < 0 || b.length < off+len) {
			throw new IndexOutOfBoundsException();
		}
		if(referenceThreshold >= 0 && len > referenceThreshold) {
			writeReference(b, off, len);
		} else {
			writeCopy(b, off, len);
		}
	}

	public void write(int b) {
		byte[] ba = new byte[1];
		ba[0] = (byte)b;
		write(ba);
	}

	@Override
	public int write(ByteBuffer src) {
		int slen = src.remaining();
		if(referenceThreshold >= 0 && slen > referenceThreshold) {
			writeCopy(src);
		} else {
			writeReference(src);
		}
		return slen;
	}

	@Override
	public synchronized long write(ByteBuffer[] srcs) {
		return write(srcs, 0, srcs.length);
	}

	@Override
	public synchronized long write(ByteBuffer[] srcs, int offset, int length) {
		if(offset < 0 || length < 0 || srcs.length < offset+length) {
			throw new IndexOutOfBoundsException();
		}
		long total = 0;
		for(int i=offset; offset < length; offset++) {
			ByteBuffer src = srcs[i];
			total += write(src);
		}
		return total;
	}

	private synchronized void writeCopy(byte[] b, int off, int len) {
		int ipos = internalBuffer.position();
		if(internalBuffer.capacity() - ipos < len) {
			// allocate new buffer
			int nsize = chunkSize > len ? chunkSize : len;
			internalBuffer = ByteBuffer.allocateDirect(nsize);
			ipos = 0;
		} else if(internalBuffer == lastInternalBuffer) {
			// optimization: concatenates to the last buffer instead
			//               of adding new reference
			ByteBuffer dup = vec.get(vec.size()-1);
			internalBuffer.put(b, off, len);
			dup.limit(ipos + len);
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

	private synchronized void writeCopy(ByteBuffer src) {
		int slen = src.remaining();
		int ipos = internalBuffer.position();
		if(internalBuffer.capacity() - ipos < slen) {
			// allocate new buffer
			int nsize = chunkSize > slen ? chunkSize : slen;
			internalBuffer = ByteBuffer.allocateDirect(nsize);
			ipos = 0;
		} else if(internalBuffer == lastInternalBuffer) {
			// optimization: concatenates to the last buffer instead
			//               of adding new reference
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

	private synchronized void writeReference(byte[] b, int off, int len) {
		ByteBuffer buf = ByteBuffer.wrap(b, off, len);
		vec.add(buf);
		lastInternalBuffer = null;
	}

	private synchronized void writeReference(ByteBuffer src) {
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

	public synchronized int read(byte[] b) {
		return read(b, 0, b.length);
	}

	public synchronized int read(byte[] b, int off, int len) {
		if(off < 0 || len < 0 || b.length < off+len) {
			throw new IndexOutOfBoundsException();
		}
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

	public synchronized int read() {
		byte[] ba = new byte[1];
		if(read(ba) >= 1) {
			return ba[0];
		} else {
			return -1;
		}
	}

	@Override
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

	@Override
	public synchronized long read(ByteBuffer[] dsts) {
		return read(dsts, 0, dsts.length);
	}

	@Override
	public synchronized long read(ByteBuffer[] dsts, int offset, int length) {
		if(offset < 0 || length < 0 || dsts.length < offset+length) {
			throw new IndexOutOfBoundsException();
		}
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
		if(len <= 0) {
			return 0;
		}
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


	public final static class OutputStream extends java.io.OutputStream {
		private VectoredByteBuffer vbb;

		OutputStream(VectoredByteBuffer vbb) {
			this.vbb = vbb;
		}

		@Override
		public void write(byte[] b) {
			vbb.write(b);
		}

		@Override
		public void write(byte[] b, int off, int len) {
			vbb.write(b, off, len);
		}

		@Override
		public void write(int b) {
			vbb.write(b);
		}

		public int write(ByteBuffer src) {
			return vbb.write(src);
		}

		public long write(ByteBuffer[] srcs) {
			return vbb.write(srcs);
		}

		public long write(ByteBuffer[] srcs, int offset, int length) {
			return vbb.write(srcs, offset, length);
		}

		public void writeTo(OutputStream out) throws IOException {
			vbb.writeTo(out);
		}

		public byte[] toByteArray() {
			return vbb.toByteArray();
		}
	}

	public final static class InputStream extends java.io.InputStream {
		private VectoredByteBuffer vbb;

		InputStream(VectoredByteBuffer vbb) {
			this.vbb = vbb;
		}

		@Override
		public int available() {
			return vbb.available();
		}

		@Override
		public int read(byte[] b) {
			return vbb.read(b);
		}

		@Override
		public int read(byte[] b, int off, int len) {
			return vbb.read(b, off, len);
		}

		@Override
		public int read() {
			return vbb.read();
		}

		public int read(ByteBuffer dst) {
			return vbb.read(dst);
		}

		public long read(ByteBuffer[] dsts, int offset, int length) {
			return vbb.read(dsts, offset, length);
		}

		public long read(GatheringByteChannel to) throws IOException {
			return vbb.read(to);
		}

		public long skip(long len) {
			return vbb.skip(len);
		}
	}

	public OutputStream outputStream() {
		return new OutputStream(this);
	}

	public InputStream inputStream() {
		return new InputStream(this);
	}
}

