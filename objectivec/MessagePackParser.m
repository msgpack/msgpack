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

//  MessagePackParser.m
//  Created by Sugendran Ganess and Chris Hulbert

#import "MessagePackParser.h"
#include "msgpack_src/msgpack.h"

@implementation MessagePackParser

// This function returns a parsed object that you have the responsibility to release/autorelease (see 'create rule' in apple docs)
+(id) createUnpackedObject:(msgpack_object)obj {
    switch (obj.type) {
        case MSGPACK_OBJECT_BOOLEAN:
            return [[NSNumber alloc] initWithBool:obj.via.boolean];
            break;
        case MSGPACK_OBJECT_POSITIVE_INTEGER:
            return [[NSNumber alloc] initWithUnsignedLongLong:obj.via.u64];
            break;
        case MSGPACK_OBJECT_NEGATIVE_INTEGER:
            return [[NSNumber alloc] initWithLongLong:obj.via.i64];
            break;
        case MSGPACK_OBJECT_DOUBLE:
            return [[NSNumber alloc] initWithDouble:obj.via.dec];
            break;
        case MSGPACK_OBJECT_RAW:
            return [[NSString alloc] initWithBytes:obj.via.raw.ptr length:obj.via.raw.size encoding:NSUTF8StringEncoding];
            break;
        case MSGPACK_OBJECT_ARRAY:
        {
            NSMutableArray *arr = [[NSMutableArray alloc] initWithCapacity:obj.via.array.size];
            msgpack_object* const pend = obj.via.array.ptr + obj.via.array.size;
            for(msgpack_object *p= obj.via.array.ptr;p < pend;p++){
				id newArrayItem = [self createUnpackedObject:*p];
                [arr addObject:newArrayItem];
				[newArrayItem release];
            }
            return arr;
        }
            break;
        case MSGPACK_OBJECT_MAP:
        {
            NSMutableDictionary *dict = [[NSMutableDictionary alloc] initWithCapacity:obj.via.map.size];
            msgpack_object_kv* const pend = obj.via.map.ptr + obj.via.map.size;
            for(msgpack_object_kv* p = obj.via.map.ptr; p < pend; p++){
                id key = [self createUnpackedObject:p->key];
                id val = [self createUnpackedObject:p->val];
                [dict setValue:val forKey:key];
				[key release];
				[val release];
            }
            return dict;
        }
            break;
        case MSGPACK_OBJECT_NIL:
        default:
            return [NSNull null]; // Since nsnull is a system singleton, we don't have to worry about ownership of it
            break;
    }
}

// Parse the given messagepack data into a NSDictionary or NSArray typically
+ (id)parseData:(NSData*)data {
	msgpack_unpacked msg;
	msgpack_unpacked_init(&msg);
	bool success = msgpack_unpack_next(&msg, data.bytes, data.length, NULL); // Parse it into C-land
	id results = success ? [self createUnpackedObject:msg.data] : nil; // Convert from C-land to Obj-c-land
	msgpack_unpacked_destroy(&msg); // Free the parser
	return [results autorelease];
}

@end
