// Copyright 2011 Media Innovations
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//  NSData+MessagePack.h
//  Created by Chris Hulbert on 23/06/11.

#import <Foundation/Foundation.h>

// Adds MessagePack parsing to NSData
@interface NSData (NSData_MessagePack)

// Parses the receiver's data into a message pack array or dictionary
- (id)messagePackParse;

@end
