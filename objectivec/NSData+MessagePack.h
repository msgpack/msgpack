//
//  NSData+MessagePack.h
//  Fetch TV Remote
//
//  Created by Chris Hulbert on 23/06/11.
//  Copyright 2011 Digital Five. All rights reserved.
//

#import <Foundation/Foundation.h>

// Adds MessagePack parsing to NSData
@interface NSData (NSData_MessagePack)

// Parses the receiver's data into a message pack array or dictionary
- (id)messagePackParse;

@end
