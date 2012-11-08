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

	/**
	 * Base class of encoder and decoder classes.
	 * It defines a TypeMap instance, which is the class that manages the encoding/decoding of each type of object.
	 * @see TypeMap
	 */
	public class MessagePackBase
	{
		/**
		 * TypeMap instance to be used with the current encoder/decoder instance.
		 */
		protected var _typeMap:TypeMap;

		/**
		 * Constructor of this abstract class.
		 * @param _typeMap TypeMap instance related to this instance. If this value is null, a default TypeMap instance is used.
		 */
		public function MessagePackBase(_typeMap:TypeMap = null)
		{
			this._typeMap = _typeMap || TypeMap.global;
		}

		/**
		 * Get the current TypeMap instance.
		 */
		public function get typeMap():TypeMap
		{
			return _typeMap;
		}
	}
}