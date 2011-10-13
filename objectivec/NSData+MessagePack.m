//
//  NSData+MessagePack.m
//  Fetch TV Remote
//
//  Created by Chris Hulbert on 23/06/11.
//  Copyright 2011 Digital Five. All rights reserved.
//

#import "NSData+MessagePack.h"

#import "MessagePackParser.h"

@implementation NSData (NSData_MessagePack)

-(id)messagePackParse {
	return [MessagePackParser parseData:self];
}

@end
