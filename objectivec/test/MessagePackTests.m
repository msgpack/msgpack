//
//  MessagePackTests.h
//  MessagePackTests
//
//  Created by Keisuke Matsuo on 11/12/11.
//  Copyright (c) 2011 Keisuke Matsuo. All rights reserved.
//

#import "MessagePackTests.h"
#import "MessagePack.h"

@implementation MessagePackTests

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
    float input = 3.140001f;
    float expect = input;
    NSLog(@"input:%f expect:%f", input, expect);
    
    NSDictionary *inputDic = [NSDictionary dictionaryWithObjectsAndKeys:
                           [NSNumber numberWithFloat:input], @"floatVal",
                           nil];
    NSDictionary *resultDic = [[inputDic messagePack] messagePackParse];
    float result = [[resultDic objectForKey:@"floatVal"] floatValue];
    
    STAssertEquals(result, expect, @"3.140001");
}

- (void)testDouble
{
    double input = 3.140000000000001;
    double expect = input;

    NSDictionary *inputDic = [NSDictionary dictionaryWithObjectsAndKeys:
                           [NSNumber numberWithDouble:input], @"doubleVal",
                           nil];
    NSDictionary *resultDic = [[inputDic messagePack] messagePackParse];
    double result = [[resultDic objectForKey:@"doubleVal"] doubleValue];

    STAssertEquals(result, expect, @"3.140000000000001");
}

@end
