%%
%% MessagePack for Erlang
%%
%% Copyright (C) 2009-2010 UENISHI Kota
%%
%%    Licensed under the Apache License, Version 2.0 (the "License");
%%    you may not use this file except in compliance with the License.
%%    You may obtain a copy of the License at
%%
%%        http://www.apache.org/licenses/LICENSE-2.0
%%
%%    Unless required by applicable law or agreed to in writing, software
%%    distributed under the License is distributed on an "AS IS" BASIS,
%%    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%%    See the License for the specific language governing permissions and
%%    limitations under the License.

-module(msgpack).
-author('kuenishi+msgpack@gmail.com').

%% tuples, atoms are not supported. lists, integers, double, and so on.
%% see http://msgpack.sourceforge.jp/spec for
%% supported formats. APIs are almost compatible
%% for C API (http://msgpack.sourceforge.jp/c:doc)
%% except buffering functions (both copying and zero-copying).
-export([pack/1, unpack/1, unpack_all/1]).

% compile:
% erl> c(msgpack).
% erl> S = <some term>.
% erl> {S, <<>>} = msgpack:unpack( msgpack:pack(S) ).
-type reason() ::  enomem | badarg | no_code_matches.
-type map() :: any(). % there's no 'dict' type...
-type msgpack_term() :: [msgpack_term()] | integer() | float() | {dict, map()}.

% ===== external APIs ===== %
-spec pack(Term::msgpack_term()) -> binary().
pack(O) when is_integer(O) andalso O < 0 ->
    pack_int_(O);
pack(O) when is_integer(O) ->
    pack_uint_(O);
pack(O) when is_float(O) ->
    pack_double(O);
pack(nil) ->
    pack_nil();
pack(Bool) when is_atom(Bool) ->
    pack_bool(Bool);
pack(Bin) when is_binary(Bin) ->
    pack_raw(Bin);
pack(List)  when is_list(List) ->
    pack_array(List);
pack({dict, Map}) ->
    pack_map({dict, Map});
pack(_) ->
    undefined.

% unpacking.
% if failed in decoding and not end, get more data
% and feed more Bin into this function.
% TODO: error case for imcomplete format when short for any type formats.
-spec unpack( binary() )-> 
    {msgpack_term(), binary()} | {more, non_neg_integer()} | {error, reason()}.
unpack(Bin) when not is_binary(Bin)->
    {error, badarg};
unpack(Bin) when bit_size(Bin) >= 8 ->
    << Flag:8/unsigned-integer, Payload/binary >> = Bin,
    unpack_(Flag, Payload);
unpack(<<>>)-> % when bit_size(Bin) < 8 ->
    {more, 1}.

-spec unpack_all( binary() ) -> [msgpack_term()].
unpack_all(Data)->
    case unpack(Data) of
	{ Term, Binary } when bit_size(Binary) =:= 0 ->
	    [Term];
	{ Term, Binary } when is_binary(Binary) ->
	    [Term|unpack_all(Binary)]
    end.


% ===== internal APIs ===== %

% positive fixnum
pack_uint_(N) when is_integer( N ) , N < 128 ->  
    << 2#0:1, N:7 >>;
% uint 8
pack_uint_( N ) when is_integer( N ) andalso N < 256 ->
    << 16#CC:8, N:8 >>;

% uint 16
pack_uint_( N ) when is_integer( N ) andalso N < 65536 ->
    << 16#CD:8, N:16/big-unsigned-integer-unit:1 >>;

% uint 32
pack_uint_( N ) when is_integer( N ) andalso N < 16#FFFFFFFF->
    << 16#CE:8, N:32/big-unsigned-integer-unit:1 >>;

% uint 64
pack_uint_( N ) when is_integer( N )->
    << 16#CF:8, N:64/big-unsigned-integer-unit:1 >>.

% negative fixnum
pack_int_( N ) when is_integer( N ) , N >= -32->
    << 2#111:3, N:5 >>;
% int 8
pack_int_( N ) when is_integer( N ) , N >= -256 ->
    << 16#D0:8, N:8 >>;
% int 16
pack_int_( N ) when is_integer( N ), N >= -65536 ->
    << 16#D1:8, N:16/big-signed-integer-unit:1 >>;
% int 32
pack_int_( N ) when is_integer( N ), N >= -16#FFFFFFFF ->
    << 16#D2:8, N:32/big-signed-integer-unit:1 >>;
% int 64
pack_int_( N ) when is_integer( N )->
    << 16#D3:8, N:64/big-signed-integer-unit:1 >>.

% nil
pack_nil()->
    << 16#C0:8 >>.
% pack_true / pack_false
pack_bool(true)->    << 16#C3:8 >>;
pack_bool(false)->   << 16#C2:8 >>.

% float : erlang's float is always IEEE 754 64bit format.
%pack_float(F) when is_float(F)->
%    << 16#CA:8, F:32/big-float-unit:1 >>.
%    pack_double(F).
% double
pack_double(F) when is_float(F)->
    << 16#CB:8, F:64/big-float-unit:1 >>.

% raw bytes
pack_raw(Bin) when is_binary(Bin)->
    MaxLen = 16#10000, % 65536
    case byte_size(Bin) of
	Len when Len < 6->
	    << 2#101:3, Len:5, Bin/binary >>;
	Len when Len < MaxLen ->
	    << 16#DA:8, Len:16/big-unsigned-integer-unit:1, Bin/binary >>;
	Len ->
	    << 16#DB:8, Len:32/big-unsigned-integer-unit:1, Bin/binary >>
    end.

% list / tuple
pack_array(L) when is_list(L)->
    MaxLen = 16#10000, %65536
    case length(L) of
 	Len when Len < 16 ->
 	    << 2#1001:4, Len:4/integer-unit:1, (pack_array_(L))/binary >>;
	Len when Len < MaxLen ->
	    << 16#DC:8, Len:16/big-unsigned-integer-unit:1,(pack_array_(L))/binary >>;
	Len ->
	    << 16#DD:8, Len:32/big-unsigned-integer-unit:1,(pack_array_(L))/binary >>
    end.
pack_array_([])-> <<>>;
pack_array_([Head|Tail])->
    << (pack(Head))/binary, (pack_array_(Tail))/binary >>.

% FIXME! this should be tail-recursive and without lists:reverse/1
unpack_array_(<<>>, 0, RetList)   -> {lists:reverse(RetList), <<>>};
unpack_array_(Remain, 0, RetList) when is_binary(Remain)-> {lists:reverse(RetList), Remain};
unpack_array_(<<>>, RestLen, _RetList) when RestLen > 0 ->  {more, RestLen};
unpack_array_(Bin, RestLen, RetList) when is_binary(Bin)->
    case unpack(Bin) of
	{more, Len} -> {more, Len+RestLen-1};
	{Term, Rest}->
	    unpack_array_(Rest, RestLen-1, [Term|RetList])
    end.

% FIXME: write test for pack_map/1
pack_map({dict,M})->
    MaxLen = 16#10000, %65536
    case dict:size(M) of
	Len when Len < 16 ->
 	    << 2#1001:4, Len:4/integer-unit:1, (pack_map_(dict:to_list(M))) >>;
	Len when Len < MaxLen ->
	    << 16#DE:8, Len:16/big-unsigned-integer-unit:1, (pack_map_(dict:to_list(M))) >>;
	Len ->
	    << 16#DF:8, Len:32/big-unsigned-integer-unit:1, (pack_map_(dict:to_list(M))) >>
    end.

pack_map_([])-> <<>>;
pack_map_([{Key,Value}|Tail]) ->
    << (pack(Key)),(pack(Value)),(pack_map_(Tail)) >>.

% FIXME: write test for unpack_map/1
-spec unpack_map_(binary(), non_neg_integer(), [{term(), msgpack_term()}])->
    {more, non_neg_integer()} | { any(), binary()}.
unpack_map_(Bin,  0,  Dict) when is_binary(Bin) -> { {dict, Dict}, Bin};
unpack_map_(Bin, Len, Dict) when is_binary(Bin) and is_integer(Len) ->
    case unpack(Bin) of
	{ more, MoreLen } -> { more, MoreLen+Len-1 };
	{ Key, Rest } ->
	    case unpack(Rest) of
		{more, MoreLen} -> { more, MoreLen+Len-1 };
		{ Value, Rest2 }->
		    unpack_map_(Rest2,Len-1,dict:append(Key,Value,Dict))
	    end
    end.

% {more, <remaining byte size>
-spec unpack_(Flag::integer(), Payload::binary())->
    {more, pos_integer()} | {msgpack_term(), binary()} | {error, reason()}.
unpack_(Flag, Payload)->
    PayloadLen = byte_size(Payload),
    case Flag of 
	16#C0 ->
	    {nil, Payload};
	16#C2 ->
	    {false, Payload};
	16#C3 ->
	    {true, Payload};

	16#CA when PayloadLen >= 4 -> % 32bit float
	    << Return:32/float-unit:1, Rest/binary >> = Payload,
	    {Return, Rest};
	16#CA ->
	    {more, 4-PayloadLen}; % at least more

	16#CB when PayloadLen >= 8 -> % 64bit float
	    << Return:64/float-unit:1, Rest/binary >> = Payload,
	    {Return, Rest};
	16#CB ->
	    {more, 8-PayloadLen};

	16#CC when PayloadLen >= 1 -> % uint 8
	    << Int:8/unsigned-integer, Rest/binary >> = Payload,
	    {Int, Rest};
	16#CC ->
	    {more, 1};

	16#CD when PayloadLen >= 2 -> % uint 16
	    << Int:16/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#CD ->
	    {more, 2-PayloadLen};

	16#CE when PayloadLen >= 4 ->
	    << Int:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#CE ->
	    {more, 4-PayloadLen}; % at least more

	16#CF when PayloadLen >= 8 ->
	    << Int:64/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#CF ->
	    {more, 8-PayloadLen};

	16#D0 when PayloadLen >= 1 -> % int 8
	    << Int:8/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#D0 ->
	    {more, 1};

	16#D1 when PayloadLen >= 2 -> % int 16
	    << Int:16/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#D1 ->
	    {more, 2-PayloadLen};

	16#D2 when PayloadLen >= 4 -> % int 32
	    << Int:32/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#D2 ->
	    {more, 4-PayloadLen};

	16#D3 when PayloadLen >= 8 -> % int 64
	    << Int:64/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#D3 ->
	    {more, 8-PayloadLen};

	16#DA when PayloadLen >= 2 -> % raw 16
	    << Len:16/unsigned-integer-unit:1, Rest/binary >> = Payload,
	    << Return:Len/binary, Remain/binary >> = Rest,
	    {Return, Remain};
	16#DA ->
	    {more, 16-PayloadLen};

	16#DB when PayloadLen >= 4 -> % raw 32
	    << Len:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    << Return:Len/binary, Remain/binary >> = Rest,
	    {Return, Remain};
	16#DB ->
	    {more, 4-PayloadLen};

	16#DC when PayloadLen >= 2 -> % array 16
	    << Len:16/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    unpack_array_(Rest, Len, []);
	16#DC ->
	    {more, 2-PayloadLen};

	16#DD when PayloadLen >= 4 -> % array 32
	    << Len:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    unpack_array_(Rest, Len, []);
	16#DD ->
	    {more, 4-PayloadLen};

	16#DE when PayloadLen >= 2 -> % map 16
	    << Len:16/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    unpack_map_(Rest, Len, dict:new());
	16#DE ->
	    {more, 2-PayloadLen};

	16#DF when PayloadLen >= 4 -> % map 32
	    << Len:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    unpack_map_(Rest, Len, dict:new());

	% positive fixnum
	Code when Code >= 2#00000000, Code < 2#10000000->
	    {Code, Payload};

	% negative fixnum
	Code when Code >= 2#11100000 ->
	    {(Code - 16#100), Payload};

	Code when Code >= 2#10100000 , Code < 2#11000000 ->
%	 101XXXXX for FixRaw 
	    Len = Code rem 2#10100000,
	    << Return:Len/binary, Remain/binary >> = Payload,
	    {Return, Remain};

	Code when Code >= 2#10010000 , Code < 2#10100000 ->
%        1001XXXX for FixArray
	    Len = Code rem 2#10010000,
	    unpack_array_(Payload, Len, []);

	Code when Code >= 2#10000000 , Code < 2#10010000 ->
%        1000XXXX for FixMap
	    Len = Code rem 2#10000000,
	    unpack_map_(Payload, Len, dict:new());

	_Other ->
%	    erlang:display(_Other),
	    {error, no_code_matches}
    end.

% ===== test codes ===== %
-include_lib("eunit/include/eunit.hrl").
-ifdef(EUNIT).

compare_all([], [])-> ok;
compare_all([], R)-> {toomuchrhs, R};
compare_all(L, [])-> {toomuchlhs, L};
compare_all([LH|LTL], [RH|RTL]) ->
    LH=RH,
    compare_all(LTL, RTL).

test_data()->
    [0, 1, 2, 123, 512, 1230, 678908, 16#FFFFFFFFFF,
     -1, -23, -512, -1230, -567898, -16#FFFFFFFFFF,
     123.123, -234.4355, 1.0e-34, 1.0e64,
     [23, 234, 0.23],
     "hogehoge", "243546rf7g68h798j",
     <<"hoasfdafdas][">>,
     [0,42,"sum", [1,2]], [1,42, nil, [3]]
    ].

basic_test()->
    Tests = test_data(),
    Passed = test_(Tests),
    Passed = length(Tests).

port_test()->
    Tests = test_data(),
    {[Tests],<<>>} = msgpack:unpack(msgpack:pack([Tests])),
    Port = open_port({spawn, "ruby ../test/crosslang.rb"}, [binary]),
    true = port_command(Port, msgpack:pack(Tests) ),
    receive
	{Port, {data, Data}}->  {Tests, <<>>}=msgpack:unpack(Data)
    after 1024-> ?assert(false)   end,
    port_close(Port).

test_p(Len,Term,OrigBin,Len) ->
    {Term, <<>>}=msgpack:unpack(OrigBin);
test_p(I,_,OrigBin,Len) when I < Len->
    <<Bin:I/binary, _/binary>> = OrigBin,
    {more, N}=msgpack:unpack(Bin),
    ?assert(0 < N),
    ?assert(N < Len).

partial_test()-> % error handling test.
    Term = lists:seq(0, 45),
    Bin=msgpack:pack(Term),
    BinLen = byte_size(Bin),
    [test_p(X, Term, Bin, BinLen) || X <- lists:seq(0,BinLen)].

long_test()->
    Longer = lists:seq(0, 655), %55),
%%     Longest = lists:seq(0,12345),
    {Longer, <<>>} = msgpack:unpack(msgpack:pack(Longer)).
%%     {Longest, <<>>} = msgpack:unpack(msgpack:pack(Longest)).

unknown_test()->
    Tests = [0, 1, 2, 123, 512, 1230, 678908,
	     -1, -23, -512, -1230, -567898,
	     <<"hogehoge">>, <<"243546rf7g68h798j">>,
%	     123.123,  %FIXME
%            -234.4355, 1.0e-34, 1.0e64, % FIXME
	     [23, 234, 0.23],
	     [0,42,<<"sum">>, [1,2]], [1,42, nil, [3]],
	     42
	    ],
    Port = open_port({spawn, "ruby testcase_generator.rb"}, [binary]),
    receive
	{Port, {data, Data}}->
	    compare_all(Tests, msgpack:unpack_all(Data))
    after 1024-> ?assert(false)   end,
    port_close(Port).

test_([]) -> 0;
test_([S|Rest])->
    Pack = msgpack:pack(S),
    {S, <<>>} = msgpack:unpack( Pack ),
%    ?debugVal( hoge ),
    1+test_(Rest).

other_test()->
    {more,1}=msgpack:unpack(<<>>).

-endif.
