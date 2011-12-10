//
//  testTests.m
//  testTests
//
//  Created by Keisuke Matsuo on 11/12/11.
//  Copyright (c) 2011年 Keisuke Matsuo. All rights reserved.
//

#import "testTests.h"
#import "MessagePack.h"

@implementation testTests

- (void)setUp
{
    [super setUp];
    
    // Set-up code here.
}

- (void)tearDown
{
    // Tear-down code here.
    
    [super tearDown];
}

- (void)testFloat
{
    NSNumber *expect = [NSNumber numberWithFloat:3.140000f];
    NSDictionary *input = [NSDictionary dictionaryWithObjectsAndKeys:
                           expect, @"floatVal",
                           nil];
    NSNumber *result = [[[input messagePack] messagePackParse] objectForKey:@"floatVal"];
    
    NSLog(@"result:%@ expect:%@",result, expect);
    STAssertEqualObjects([result description], [expect description], @"3.140000");
}

- (void)testDouble
{
    NSNumber *expect = [NSNumber numberWithDouble:3.140000000000001];
    NSDictionary *input = [NSDictionary dictionaryWithObjectsAndKeys:
                           expect, @"doubleVal",
                           nil];
    NSNumber *result = [[[input messagePack] messagePackParse] objectForKey:@"doubleVal"];
    
    NSLog(@"result:%@ expect:%@",result, expect);
    STAssertEqualObjects([result description], [expect description], @"3.140000000000001");
}

@end
