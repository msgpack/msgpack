%%
%% MessagePack for Erlang
%%
%% Copyright (C) 2009 UENISHI Kota
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

-export([pack/1, unpack/1, unpack_all/1, test/0]).

-include_lib("eunit/include/eunit.hrl").

% compile:
% erl> c(msgpack).
% erl> S = <some term>.
% erl> {S, <<>>} = msgpack:unpack( msgpack:pack(S) ).

%% tuples, atoms are not supported.  lists, integers, double, and so on.
%% see http://msgpack.sourceforge.jp/spec for
%% supported formats. APIs are almost compatible
%% for C API (http://msgpack.sourceforge.jp/c:doc)
%% except buffering functions (both copying and zero-copying).
-export([
	 pack_nil/0,
	 pack_bool/1,
	 pack_float/1,
	 pack_double/1,
	 pack_raw/1,
	 pack_array/1,
	 pack_map/1,
	 pack_object/1	]).

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
pack_float(F) when is_float(F)->
%    << 16#CA:8, F:32/big-float-unit:1 >>.
    pack_double(F).
% double
pack_double(F) when is_float(F)->
    << 16#CB:8, F:64/big-float-unit:1 >>.

power(N,0) when is_integer(N) -> 1;
power(N,D) when is_integer(N) and is_integer(D) -> N * power(N, D-1).

% raw bytes
pack_raw(Bin) when is_binary(Bin)->
    MaxLen = power(2,16),
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
    MaxLen = power(2,16),
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
    << (pack_object(Head))/binary, (pack_array_(Tail))/binary >>.

unpack_array_(<<>>, 0)-> [];
unpack_array_(Remain, 0) when is_binary(Remain)-> [Remain];
unpack_array_(Bin, RestLen) when is_binary(Bin)->
    {Term, Rest} = unpack(Bin),
    [Term|unpack_array_(Rest, RestLen-1)].
    
pack_map({dict,M})->
    MaxLen = power(2,16),
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
    << (pack_object(Key)),(pack_object(Value)),(pack_map_(Tail)) >>.

unpack_map_(<<>>, 0)-> [];
unpack_map_(Bin,  0) when is_binary(Bin)-> [Bin];
unpack_map_(Bin, Len) when is_binary(Bin) and is_integer(Len) ->
    { Key, Rest } = unpack(Bin),
    { Value, Rest2 } = unpack(Rest),
    [{Key,Value}|unpack_map_(Rest2,Len-1)].

pack_object(O) when is_integer(O) andalso O < 0 ->
    pack_int_(O);
pack_object(O) when is_integer(O) ->
    pack_uint_(O);
pack_object(O) when is_float(O)->
    pack_double(O);
pack_object(nil) ->
    pack_nil();
pack_object(Bool) when is_atom(Bool) ->
    pack_bool(Bool);
pack_object(Bin) when is_binary(Bin)->
    pack_raw(Bin);
pack_object(List)  when is_list(List)->
    pack_array(List);
pack_object({dict, Map})->
    pack_map({dict, Map});
pack_object(_) ->
    undefined.

pack(Obj)->
    pack_object(Obj).


% unpacking.
% if failed in decoding and not end, get more data 
% and feed more Bin into this function.
% TODO: error case for imcomplete format when short for any type formats.
-spec unpack( binary() )-> {term(), binary()}.
unpack(Bin) when bit_size(Bin) >= 8 ->
    << Flag:8/unsigned-integer, Payload/binary >> = Bin,
    case Flag of 
	16#C0 ->
	    {nil, Payload};
	16#C2 ->
	    {false, Payload};
	16#C3 ->
	    {true, Payload};

	16#CA -> % 32bit float
	    << Return:32/float-unit:1, Rest/binary >> = Payload,
	    {Return, Rest};
	16#CB -> % 64bit float
	    << Return:64/float-unit:1, Rest/binary >> = Payload,
	    {Return, Rest};

	16#CC -> % uint 8
	    << Int:8/unsigned-integer, Rest/binary >> = Payload,
	    {Int, Rest};
	16#CD -> % uint 16
	    << Int:16/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#CE ->
	    << Int:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#CF ->
	    << Int:64/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};

	16#D0 -> % int 8
	    << Int:8/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#D1 -> % int 16
	    << Int:16/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#D2 -> % int 32
	    << Int:32/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#D3 -> % int 64
	    << Int:64/big-signed-integer-unit:1, Rest/binary >> = Payload,
	    {Int, Rest};
	16#DA -> % raw 16
	    << Len:16/unsigned-integer-unit:1, Rest/binary >> = Payload,
	    << Return:Len/binary, Remain/binary >> = Rest,
	    {Return, Remain};
	16#DB -> % raw 32
	    << Len:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    << Return:Len/binary, Remain/binary >> = Rest,
	    {Return, Remain};
	16#DC -> % array 16
	    << Len:16/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    Array=unpack_array_(Rest, Len),
	    case length(Array) of
		Len -> {Array, <<>>};
		_ -> 
		    {Return, RemainRest} = lists:split(Len, Array),
		    [Remain] = RemainRest,
		    {Return, Remain}
	    end;
	16#DD -> % array 32
	    << Len:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    Array=unpack_array_(Rest, Len),
	    case length(Array) of
		Len -> {Array, <<>>};
		_ -> 
		    {Return, RemainRest} = lists:split(Len, Array),
		    [Remain] = RemainRest,
		    {Return, Remain}
	    end;
	16#DE -> % map 16
	    << Len:16/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    Array=unpack_map_(Rest, Len),
	    case length(Array) of
		Len -> { dict:from_list(Array), <<>>};
		_ -> 
		    {Return, RemainRest} = lists:split(Len, Array),
		    [Remain] = RemainRest,
		    {dict:from_list(Return), Remain}
	    end;
	16#DF -> % map 32
	    << Len:32/big-unsigned-integer-unit:1, Rest/binary >> = Payload,
	    Array=unpack_map_(Rest, Len),
	    case length(Array) of
		Len -> { dict:from_list(Array), <<>>};
		_ -> 
		    {Return, RemainRest} = lists:split(Len, Array),
		    [Remain] = RemainRest,
		    {dict:from_list(Return), Remain}
	    end;

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
	    Array=unpack_array_(Payload, Len),
	    case length(Array) of
		Len -> { Array, <<>>};
		_ -> 
		    {Return, RemainRest} = lists:split(Len, Array),
		    [Remain] = RemainRest,
		    {Return, Remain}
	    end;

	Code when Code >= 2#10000000 , Code < 2#10010000 ->
%        1000XXXX for FixMap
	    Len = Code rem 2#10000000,
	    Array=unpack_map_(Payload, Len),
	    case length(Array) of
		Len -> { dict:from_list(Array), <<>>};
		_ -> 
		    {Return, RemainRest} = lists:split(Len, Array),
		    [Remain] = RemainRest,
		    {dict:from_list(Return), Remain}
	    end;

	_Other ->
	    erlang:display(_Other),
	    {error, no_code_matches}
    end.
    
unpack_all(Data)->
    case unpack(Data) of
	{ Term, Binary } when bit_size(Binary) =:= 0 -> 
	    [Term];
	{ Term, Binary } when is_binary(Binary) ->
	    [Term|unpack_all(Binary)]
    end.

-ifdef(EUNIT).

test()->
    Tests = [0, 1, 2, 123, 512, 1230, 678908, 16#FFFFFFFFFF,
	     -1, -23, -512, -1230, -567898, -16#FFFFFFFFFF,
	     123.123, -234.4355, 1.0e-34, 1.0e64,
	     [23, 234, 0.23],
	     "hogehoge", "243546rf7g68h798j",
	     <<"hoasfdafdas][">>,
	     [0,42,"sum", [1,2]], [1,42, nil, [3]]
	    ],
    Passed = test_(Tests),
    Passed = length(Tests).
%%     Port = open_port({spawn, "./a.out"}, [stream]),
%%     receive {Port, {data, Data}}->
%%     io:format("~p~n", [unpack_all( list_to_binary(Data) )])
%%     after 1024-> timeout end,
%%     Passed2 = test_(Tests, Port),
%%     Passed2 = length(Tests),
%%     Port ! {self(), close},
%%     receive {Port, closed}-> ok 
%%     after 1024 -> timeout end.

test_([]) -> 0;
test_([S|Rest])->
    Pack = msgpack:pack(S),
%    io:format("testing: ~p => ~p~n", [S, Pack]),
    {S, <<>>} = msgpack:unpack( Pack ),
    test_(Rest) + 1.

-endif.
