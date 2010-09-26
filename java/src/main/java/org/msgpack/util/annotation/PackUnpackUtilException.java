package org.msgpack.util.annotation;

public class PackUnpackUtilException extends RuntimeException {

	public PackUnpackUtilException(String reason) {
		super(reason);
	}
	
	public PackUnpackUtilException(String reason, Throwable t) {
		super(reason, t);
	}
}
