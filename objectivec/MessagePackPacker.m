//
//  MessagePackPacker.m
//  Fetch TV Remote
//
//  Created by Chris Hulbert on 13/10/11.
//  Copyright (c) 2011 Digital Five. All rights reserved.
//

#import "MessagePackPacker.h"
#include "msgpack_src/msgpack.h"

@implementation MessagePackPacker

// Pack a single number, figuring out which type of number it is
+ (void)packNumber:(NSNumber*)num into:(msgpack_packer*)pk {
	CFNumberType numberType = CFNumberGetType((CFNumberRef)num);
	switch (numberType)	{
		case kCFNumberSInt8Type:
			msgpack_pack_int8(pk, num.shortValue);
			break;
		case kCFNumberSInt16Type:
		case kCFNumberShortType:
			msgpack_pack_int16(pk, num.shortValue);
			break;
		case kCFNumberSInt32Type:
		case kCFNumberIntType:
		case kCFNumberLongType:
		case kCFNumberCFIndexType:
		case kCFNumberNSIntegerType:
			msgpack_pack_int32(pk, num.intValue);
			break;
		case kCFNumberSInt64Type:
		case kCFNumberLongLongType:
			msgpack_pack_int64(pk, num.longLongValue);
			break;
		case kCFNumberFloat32Type:
		case kCFNumberFloatType:
		case kCFNumberCGFloatType:
			msgpack_pack_float(pk, num.floatValue);
			break;
		case kCFNumberFloat64Type:
		case kCFNumberDoubleType:
			msgpack_pack_double(pk, num.doubleValue);
			break;
		case kCFNumberCharType: {
			int theValue = num.intValue;
			if (theValue == 0)
				msgpack_pack_false(pk);
			else if (theValue == 1)
				msgpack_pack_true(pk);
			else
				msgpack_pack_int16(pk, theValue);
		}
			break;
		default:
			NSLog(@"Could not messagepack number, cannot recognise type: %@", num);
	}
}

// Pack a single object into the given packer
+ (void)packObject:(id)obj into:(msgpack_packer*)pk {
	if ([obj isKindOfClass:[NSArray class]]) {
		msgpack_pack_array(pk, ((NSArray*)obj).count);
		for (id arrayElement in obj) {
			[self packObject:arrayElement into:pk];
		}
	} else if ([obj isKindOfClass:[NSDictionary class]]) {
		msgpack_pack_map(pk, ((NSDictionary*)obj).count);
		for(id key in obj) {
			[self packObject:key into:pk];
			[self packObject:[obj objectForKey:key] into:pk];
		}
	} else if ([obj isKindOfClass:[NSString class]]) {
		const char *str = ((NSString*)obj).UTF8String;
		int len = strlen(str);
		msgpack_pack_raw(pk, len);
		msgpack_pack_raw_body(pk, str, len);
	} else if ([obj isKindOfClass:[NSNumber class]]) {
		[self packNumber:obj into:pk];
	} else if (obj==[NSNull null]) {
		msgpack_pack_nil(pk);
	} else {
		NSLog(@"Could not messagepack object: %@", obj);
	}
}

// Given an array or dictionary, this messagepacks it
+ (NSData*)pack:(id)obj {
	// Creates buffer and serializer instance
	msgpack_sbuffer* buffer = msgpack_sbuffer_new();
	msgpack_packer* pk = msgpack_packer_new(buffer, msgpack_sbuffer_write);
	
	// Pack the root array or dictionary node, which recurses through the rest
	[self packObject:obj into:pk];
	
	// Bridge the data back to obj-c's world
	NSData* data = [NSData dataWithBytes:buffer->data length:buffer->size];
	
	// Free
	msgpack_sbuffer_free(buffer);
	msgpack_packer_free(pk);
	
	return data;
}

@end
