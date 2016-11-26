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
	import flash.utils.IDataOutput;

	/**
	 * This class is used to encode an object to message pack format. If you want to encode standard objects you may access the default instance MessagePack.encoder.
	 * However, if you want to set a custom TypeMap instance, you'll need to create your own encoder instance.
	 * @see MessagePack
	 * @see MessagePack#encoder
	 * @see TypeMap
	 */
	public class MessagePackEncoder extends MessagePackBase
	{
		/**
		 * Create a message pack encoder instance.
		 * @param _typeMap TypeMap instance related to this instance. If this value is null, a default TypeMap instance is used.
		 */
		public function MessagePackEncoder(_typeMap:TypeMap = null)
		{
			super(_typeMap);
		}

		/**
		 * Write an object into a output buffer.
		 * @param data Object to be encoded
		 * @param output Any object that implements IDataOutput interface (ByteArray, Socket, URLStream, etc).
		 * @return Return the buffer with the encoded bytes. If output parameter is null, a ByteArray instance is created, otherwise output parameter is returned.
		 */
		public function write(data:*, output:IDataOutput = null):*
		{
			if (!output)
				output = new ByteArray();

			_typeMap.encode(data, output);

			return output;
		}
	}
}