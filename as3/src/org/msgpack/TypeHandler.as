//
// as3-msgpack (MessagePack for Actionscript3)
// Copyright (C) 2012 Lucas Teixeira (Disturbed Coder)
// 
// Contribution:
// * 2012.10.22 - ccrossley (https://github.com/ccrossley)
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
	import flash.utils.IDataInput;
	import flash.utils.IDataOutput;

	internal class TypeHandler
	{
		//
		// null handlers
		//
		public static function encodeNull(data:*, destination:IDataOutput, typeMap:TypeMap):void
		{
			destination.writeByte(0xc0);
		}

		public static function decodeNull(byte:int, source:IDataInput, typeMap:TypeMap):*
		{
			return null;
		}

		public static function checkNull(byte:int):Boolean
		{
			return byte == 0xc0;
		}

		//
		// Boolean handlers
		//
		public static function encodeBoolean(data:Boolean, destination:IDataOutput, typeMap:TypeMap):void
		{
			if (data)
				destination.writeByte(0xc3);
			else
				destination.writeByte(0xc2);
		}

		public static function decodeBoolean(byte:int, source:IDataInput, typeMap:TypeMap):Boolean
		{
			return byte == 0xc3;
		}

		public static function checkBoolean(byte:int):Boolean
		{
			return byte == 0xc3 || byte == 0xc2;
		}

		//
		// Number handlers
		//
		public static function encodeNumber(data:Number, destination:IDataOutput, typeMap:TypeMap):void
		{
			destination.writeByte(0xcb);
			destination.writeDouble(data);
		}

		public static function decodeNumber(byte:int, source:IDataInput, typeMap:TypeMap):Number
		{
			var data:Number = NaN;

			if (byte == 0xca)
				data = source.readFloat();
			else if (byte == 0xcb)
				data = source.readDouble();

			return data;
		}

		public static function checkNumber(byte:int):Boolean
		{
			return byte == 0xca || byte == 0xcb;
		}

		//
		// int handlers
		//
		public static function encodeInt(data:int, destination:IDataOutput, typeMap:TypeMap):void
		{
			if (data < -(1 << 5))
			{
				if (data < -(1 << 15))
				{
					// signed 32
					destination.writeByte(0xd2);
					destination.writeInt(data);
				}
				else if (data < -(1 << 7))
				{
					// signed 16
					destination.writeByte(0xd1);
					destination.writeShort(data);
				}
				else
				{
					// signed 8
					destination.writeByte(0xd0);
					destination.writeByte(data);
				}
			}
			else if (data < (1 << 7))
			{
				// fixnum
				destination.writeByte(data);
			}
			else
			{
				if (data < (1 << 8))
				{
					// unsigned 8
					destination.writeByte(0xcc);
					destination.writeByte(data);
				}
				else if (data < (1 << 16))
				{
					// unsigned 16
					destination.writeByte(0xcd);
					destination.writeShort(data);
				}
				else
				{
					// unsigned 32
					destination.writeByte(0xce);
					destination.writeUnsignedInt(data);
				}
			}
		}

		public static function decodeInt(byte:int, source:IDataInput, typeMap:TypeMap):int
		{
			var i:uint;
			var data:*;

			if ((byte & 0x80) == 0)
			{
				// positive fixnum
				data = byte;
			}
			else if ((byte & 0xe0) == 0xe0)
			{
				// negative fixnum
				data = byte - 0xff - 1;
			}
			else if (byte == 0xcc)
			{
				// unsigned byte
				data = source.readUnsignedByte();
			}
			else if (byte == 0xcd)
			{
				// unsigned short
				data = source.readUnsignedShort();
			}
			else if (byte == 0xce)
			{
				// unsigned int
				data = source.readUnsignedInt();
			}
			else if (byte == 0xcf)
			{
				// TODO: can't read 64 bits unsigned integers
				for (i = 0; i < 8; i++)
					source.readByte();

				data = NaN;
			}
			else if (byte == 0xd0)
			{
				// signed byte
				data = source.readByte();
			}
			else if (byte == 0xd1)
			{
				// signed short
				data = source.readShort();
			}
			else if (byte == 0xd2)
			{
				// signed int
				data = source.readInt();
			}
			else if (byte == 0xd3)
			{
				// TODO: can't read 64 bits integers
				for (i = 0; i < 8; i++)
					source.readByte();

				data = NaN;
			}

			return data;
		}

		public static function checkInt(byte:int):Boolean
		{
			return (byte & 0x80) == 0 || (byte & 0xe0) == 0xe0 || byte == 0xcc || byte == 0xcd ||
				byte == 0xce || byte == 0xcf || byte == 0xd0 || byte == 0xd1 ||
				byte == 0xd2 || byte == 0xd3;
		}

		//
		// ByteArray handlers
		//
		public static function encodeByteArray(data:ByteArray, destination:IDataOutput, typeMap:TypeMap):void
		{
			var length:uint = data.length;

			if (length < 32)
			{
				// fix raw
				destination.writeByte(0xa0 | length);
			}
			else if (length < 65536)
			{
				// raw 16
				destination.writeByte(0xda);
				destination.writeShort(length);
			}
			else
			{
				// raw 32
				destination.writeByte(0xdb);
				destination.writeInt(length);
			}

			destination.writeBytes(data);
		}

		public static function decodeByteArray(byte:int, source:IDataInput, typeMap:TypeMap):ByteArray
		{
			var length:uint;

			if ((byte & 0xe0) == 0xa0)
				length = byte & 0x1f;
			else if (byte == 0xda)
				length = source.readUnsignedShort();
			else if (byte == 0xdb)
				length = source.readUnsignedInt();

			var data:ByteArray = new ByteArray();

			if (length)
				source.readBytes(data, 0, length);

			return data;
		}

		public static function checkByteArray(byte:int):Boolean
		{
			return (byte & 0xe0) == 0xa0 || byte == 0xda || byte == 0xdb;
		}

		//
		// String handlers
		//
		public static function encodeString(data:String, destination:IDataOutput, typeMap:TypeMap):void
		{
			var bytes:ByteArray = new ByteArray();
			bytes.writeUTFBytes(data);
			typeMap.encode(bytes, destination);
		}

		//
		// XML handlers
		//
		public static function encodeXML(data:XML, destination:IDataOutput, typeMap:TypeMap):void
		{
			typeMap.encode(data.toXMLString(), destination);
		}

		//
		// Array handlers
		//
		public static function encodeArray(data:Array, destination:IDataOutput, typeMap:TypeMap):void
		{
			var length:uint = data.length;

			if (length < 16)
			{
				// fix array
				destination.writeByte(0x90 | length);
			}
			else if (length < 65536)
			{
				// array 16
				destination.writeByte(0xdc);
				destination.writeShort(length);
			}
			else
			{
				// array 32
				destination.writeByte(0xdd);
				destination.writeUnsignedInt(length);
			}

			// write elements
			for (var i:uint = 0; i < length; i++)
				typeMap.encode(data[i], destination);
		}

		public static function decodeArray(byte:int, source:IDataInput, typeMap:TypeMap):Array
		{
			var length:uint;

			if ((byte & 0xf0) == 0x90)
				length = byte & 0x0f
			else if (byte == 0xdc)
				length = source.readUnsignedShort();
			else if (byte == 0xdd)
				length = source.readUnsignedInt();

			var data:Array = [];

			for (var i:uint = 0; i < length; i++)
				data.push(typeMap.decode(source));

			return data;
		}

		public static function checkArray(byte:int):Boolean
		{
			return (byte & 0xf0) == 0x90 || byte == 0xdc || byte == 0xdd;
		}

		//
		// Object handlers
		//
		public static function encodeObject(data:Object, destination:IDataOutput, typeMap:TypeMap):void
		{
			var elements:Array = [];	

			for (var key:String in data)
				elements.push(key);

			var length:uint = elements.length;

			if (length < 16)
			{
				// fix map
				destination.writeByte(0x80 | length);
			}
			else if (length < 65536)
			{
				// map 16
				destination.writeByte(0xde);
				destination.writeShort(length);
			}
			else
			{
				// map 32
				destination.writeByte(0xdf);
				destination.writeUnsignedInt(length);
			}

			for (var i:uint = 0; i < length; i++)
			{
				var elemKey:String = elements[i];

				typeMap.encode(elemKey, destination);
				typeMap.encode(data[elemKey], destination);
			}
		}

		public static function decodeObject(byte:int, source:IDataInput, typeMap:TypeMap):Object
		{
			var length:uint;

			if ((byte & 0xf0) == 0x80)
				length = byte & 0x0f;
			else if (byte == 0xde)
				length = source.readUnsignedShort();
			else if (byte == 0xdf)
				length = source.readUnsignedInt();

			var data:Object = {};

			for (var i:uint = 0; i < length; i++)
			{
				var rawKey:* = typeMap.decode(source);
				var value:* = typeMap.decode(source);
				data[rawKey.toString()] = value;
			}

			return data;
		}

		public static function checkObject(byte:int):Boolean
		{
			return (byte & 0xf0) == 0x80 || byte == 0xde || byte == 0xdf;
		}
	}
}