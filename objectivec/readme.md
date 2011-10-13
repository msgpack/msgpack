MessagePack for Objective-C / iPhone
============

This is a wrapper for the C MessagePack parser, building the bridge to Objective-C.
In a similar way to the JSON framework, this parses MessagePack into NSDictionaries, NSArrays, NSNumbers, NSStrings, and NSNulls.
This contains a small patch to the C library so that it doesn't segfault with a byte alignment error when running on the iPhone in armv7 mode.
Please note that the parser has been extensively tested, however the packer has not been. Please get in touch if it has issues.

Parsing Usage
-----

	#import "MessagePack.h"
	...
	NSData* myData = ...
	NSDictionary* parsed = [myData messagePackParse];
	NSLog(@"%@", [parsed description]);

Packing Usage
----

    #import "MessagePack.h"
    ..
    NSData* packed = [someArray messagePack];
    NSData* packed = [someDictionary messagePack];

Authors
-------

* Sugendran Ganess
* Chris Hulbert

License
-------

	Copyright 2011 Media Innovations

	Licensed under the Apache License, Version 2.0 (the "License");
	you may not use this file except in compliance with the License.
	You may obtain a copy of the License at

	    http://www.apache.org/licenses/LICENSE-2.0

	Unless required by applicable law or agreed to in writing, software
	distributed under the License is distributed on an "AS IS" BASIS,
	WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
	See the License for the specific language governing permissions and
	limitations under the License.
