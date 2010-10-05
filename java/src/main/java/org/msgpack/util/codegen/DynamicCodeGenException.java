package org.msgpack.util.codegen;

public class DynamicCodeGenException extends RuntimeException {

	public DynamicCodeGenException(String reason) {
		super(reason);
	}

	public DynamicCodeGenException(String reason, Throwable t) {
		super(reason, t);
	}
}
