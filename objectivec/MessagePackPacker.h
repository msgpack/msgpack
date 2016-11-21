//
//  MessagePackPacker.h
//  Fetch TV Remote
//
//  Created by Chris Hulbert on 13/10/11.
//  Copyright (c) 2011 Digital Five. All rights reserved.
//

#import <Foundation/Foundation.h>

@interface MessagePackPacker : NSObject

// Given an array or dictionary, this messagepacks it
+ (NSData*)pack:(id)obj;

@end
