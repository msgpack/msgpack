///
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
	import flash.utils.IDataInput;

	/**
	 * This class is used to decode an object from message pack format. If you want to decode standard objects you may access the default instance MessagePack.decoder.
	 * However, if you want to set a custom TypeMap instance, you'll need to create your own decoder instance.
	 * @see MessagePack
	 * @see MessagePack#decoder
	 * @see TypeMap
	 */
	public class MessagePackDecoder extends MessagePackBase
	{
		/**
		 * Create a message pack decoder instance.
		 * @param _typeMap TypeMap instance related to this instance. If this value is null, a default TypeMap instance is used.
		 */
		public function MessagePackDecoder(_typeMap:TypeMap = null)
		{
			super(_typeMap);
		}

		/**
		 * Write buffer into a object.
		 * @param input Any object that implements IDataInput interface (ByteArray, Socket, URLStream, etc).
		 * @return Return the decoded object.
		 */
		public function read(input:IDataInput):*
		{
			return _typeMap.decode(input);
		}
	}
}