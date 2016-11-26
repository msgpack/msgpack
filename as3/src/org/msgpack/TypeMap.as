//
// as3-msgpack (MessagePack for Actionscript3)
// Copyright (C) 2012 Lucas Teixeira (Disturbed Coder)
// 
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
package org.msgpack
{
	import flash.utils.ByteArray;
	import flash.utils.getQualifiedClassName;
	import flash.utils.IDataInput;
	import flash.utils.IDataOutput;

	/**
	 * Each instance of TypeMap holds references for various handlers functions.
	 * Default handlers are:
	 * <li>null</li>
	 * <li>Boolean</li>
	 * <li>Number</li>
	 * <li>int</li>
	 * <li>ByteArray</li>
	 * <li>String (packed into bytes - a ByteArray)</li>
	 * <li>XML (packed into a String - which is packed into a ByteArray)</li>
	 * <li>Array</li>
	 * <li>Object (dictionary-style)</li>
	 * @see MessagePackBase
	 * @see MessagePackEncoder
	 * @see MessagePackDecoder
	 */
	public class TypeMap
	{
		/**
		 * Standard TypeMap object. Is used by the default encoder/decoder.
		 * @see MessagePack#encoder
		 * @see MessagePack#decoder
		 */
		internal static var global:TypeMap = new TypeMap();

		private var map:Object;

		/**
		 * Create a new TypeMap object
		 */
		public function TypeMap()
		{
			map = {};

			assign(null, TypeHandler.encodeNull, TypeHandler.decodeNull, TypeHandler.checkNull);
			assign(Boolean, TypeHandler.encodeBoolean, TypeHandler.decodeBoolean, TypeHandler.checkBoolean);
			assign(Number, TypeHandler.encodeNumber, TypeHandler.decodeNumber, TypeHandler.checkNumber);
			assign(int, TypeHandler.encodeInt, TypeHandler.decodeInt, TypeHandler.checkInt);
			assign(ByteArray, TypeHandler.encodeByteArray, TypeHandler.decodeByteArray, TypeHandler.checkByteArray);
			assign(String, TypeHandler.encodeString, null, null);
			assign(XML, TypeHandler.encodeXML, null, null);
			assign(Array, TypeHandler.encodeArray, TypeHandler.decodeArray, TypeHandler.checkArray);
			assign(Object, TypeHandler.encodeObject, TypeHandler.decodeObject, TypeHandler.checkObject);
		}

		/**
		 * Assign handler functions for a custom class.
		 * @param handlerEncoder Function to encode the related class type. Default signature is myEncoder(data:*, destination:IDataOutput, typeMap:TypeMap):void
		 * @param handlerDecoder Function to decode the related class type. Default signature is myDecoder(byte:int, source:IDataInput, typeMap:TypeMap):*
		 * @param handlerChecker Function to check if the following data is of the related type. Default signature is myChecker(byte:int):Boolean
		 */
		public function assign(type:Class, handlerEncoder:Function, handlerDecoder:Function, handlerChecker:Function):void
		{
			var typeName:String = getQualifiedClassName(type);
			map[typeName] = {encoder: handlerEncoder, decoder: handlerDecoder, checker: handlerChecker};
		}

		/**
		 * Unassign all handlers for a custom class.
		 */
		public function unassign(type:Class):void
		{
			var typeName:String = getQualifiedClassName(type);
			map[typeName] = undefined;
		}

		/**
		 * Write an encoded object into a buffer.
		 * @param data Object to encode
		 * @param destination Any object that implements IDataOutput interface (ByteArray, Socket, URLStream, etc).
		 */
		public function encode(data:*, destination:IDataOutput):void
		{
			var typeName:String = data == null ? "null" : getQualifiedClassName(data);
			var handler:Object = map[typeName];

			if (handler == null)
				throw new Error("MessagePack handler for type " + typeName + " not found");

			if (handler["encoder"] == null)
				throw new Error("MessagePack handler for type " + typeName + " does not have an encoder function");

			handler["encoder"](data, destination, this);
		}

		/**
		 * Read an encoded object from a buffer.
		 * @param source Any object that implements IDataInput interface (ByteArray, Socket, URLStream, etc).
		 */
		public function decode(source:IDataInput):*
		{
			var byte:int = source.readByte() & 0xff;

			for (var typeName:String in map)
			{
				var handler:Object = map[typeName];

				if (handler["checker"] != null && handler["checker"](byte) && handler["decoder"] != null)
					return handler["decoder"](byte, source, this);
			}

			throw new Error("MessagePack handler for signature 0x" + byte.toString(16) + " not found");
		}
	}
}