package org.msgpack;

import java.io.IOException;
import java.util.Iterator;
import java.util.NoSuchElementException;

public class UnpackIterator implements Iterator<Object> {
	private Unpacker pac;
	private boolean have;
	private Object data;

	UnpackIterator(Unpacker pac)
	{
		this.pac = pac;
		this.have = false;
	}

	public boolean hasNext()
	{
		if(have) { return true; }
		try {
			while(true) {
				if(pac.execute()) {
					data = pac.getData();
					pac.reset();
					have = true;
					return true;
				}

				if(!pac.fill()) {
					return false;
				}
			}
		} catch (IOException e) {
			return false;
		}
	}

	public Object next()
	{
		if(!have) {
			throw new NoSuchElementException();
		}
		have = false;
		return data;
	}

	public void remove()
	{
		throw new UnsupportedOperationException();
	}
}

