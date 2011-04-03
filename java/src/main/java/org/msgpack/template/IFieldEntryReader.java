package org.msgpack.template;

public interface IFieldEntryReader {
	
	public IFieldEntry[] convertFieldEntries(Class<?> targetClass, FieldList flist) throws NoSuchFieldException;
	public IFieldEntry[] readFieldEntries(Class<?> targetClass, FieldOption implicitOption);
	public FieldOption readImplicitFieldOption(Class<?> targetClass) ;
}
