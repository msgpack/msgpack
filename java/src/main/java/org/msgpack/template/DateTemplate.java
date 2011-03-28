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
 * 
 * 
 * @author takeshita
 */
public abstract class DateTemplate implements Template{
	
	
	public static DateTemplate getInstance() {
		return instance;
	}

	private static DateTemplate instance = new DateUnixMilliSecTemplate();
	
	static {
		TemplateRegistry.register(Date.class, instance);
	}
	
	/**
	 * replace DateTemplate
	 * @anotherTemplate 
	 */
	public static void replaceDateTemplate(DateTemplate anotherTemplate){
	
		instance = anotherTemplate;
		TemplateRegistry.register(Date.class,anotherTemplate);
		Templates.TDate = instance;
		
	}
	
	
}