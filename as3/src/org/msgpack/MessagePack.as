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
	 * MessagePack static class.
	 * Using this class you can access the encoder/decoder default objects.
	 * However you may need to created your own objects, in the case you need a custom TypeMap.
	 * Use this class when you'll use the default object handlers.
	 * @see MessagePackEncoder
	 * @see MessagePackDecoder
	 * @see TypeMap
	 */
	public class MessagePack
	{
		/**
		 * Major version value.
		 */
		public static const MAJOR:uint = 0;
		/**
		 * Minor version value.
		 */
		public static const MINOR:uint = 4;
		/**
		 * Revision version value;
		 */
		public static const REVISION:uint = 1;

		/**
		 * Get full version as a string.
		 * @return Full version string.
		 */
		public static function get VERSION():String
		{
			return MAJOR + "." + MINOR + "." + REVISION;
		}

		/**
		 * Standard decoder object.
		 */
		public static const decoder:MessagePackDecoder = new MessagePackDecoder();
		/**
		 * Standard encoder object.
		 */
		public static const encoder:MessagePackEncoder = new MessagePackEncoder();
	}
}