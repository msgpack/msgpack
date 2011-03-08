//
// MessagePack for Java
//
// Copyright (C) 2009-2010 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
package org.msgpack.template;


import org.msgpack.*;

import java.io.IOException;
import java.util.Date;

/**
 * Serialize date class to long that is elapsed seconds from Unix time.
 * This template is convinient if your system collaborate with python or / and ruby.
 * User: takeshita
 * Date: 11/03/08
 * Time: 17:56
 * To change this template use File | Settings | File Templates.
 */
public class DateUnixSecTemplate extends DateTemplate{
	
	
	
	public DateUnixSecTemplate(){}

    public Object convert(MessagePackObject messagePackObject, Object o) throws MessageTypeException {
        return new Date(messagePackObject.asLong() * 1000);
    }

    public void pack(Packer packer, Object o) throws IOException {
        try{
		    packer.packLong(((Date)o).getTime() / 1000);
    	}catch(NullPointerException e){
        	throw new MessageTypeException("target is null.", e);
        }
    }

    public Object unpack(Unpacker unpacker, Object o) throws IOException, MessageTypeException {
        return new Date(unpacker.unpackLong() * 1000);
    }
}