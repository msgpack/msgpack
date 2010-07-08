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
%% see http://msgpack.sourceforge.jp/spec for supported formats.
%% APIs are almost compatible with C API (http://msgpack.sourceforge.jp/c:doc)
%% except buffering functions (both copying and zero-copying).
-export([pack/1, unpack/1, unpack_all/1]).
-export([pack_map/1]).

% compile:
% erl> c(msgpack).
% erl> S = <some term>.
% erl> {S, <<>>} = msgpack:unpack( msgpack:pack(S) ).
-type reason() ::  enomem | badarg | no_code_matches | undefined.
-type msgpack_term() :: [msgpack_term()]
		      | {[{msgpack_term(),msgpack_term()}]}
		      | integer() | float() | binary().

% ===== external APIs ===== %
-spec pack(Term::msgpack_term()) -> binary() | {error, reason()}.
pack(Term)->
    try
	pack_(Term)
    catch
	error:Error when is_tuple(Error), element(1, Error) =:= error ->
	    Error;
	throw:Exception ->
	    erlang:display(Exception),
	    {error, Exception}
    end.

% unpacking.
% if failed in decoding and not end, get more data
% and feed more Bin into this function.
% TODO: error case for imcomplete format when short for any type formats.
-spec unpack( Bin::binary() )-> {msgpack_term(), binary()} | {error, reason()}.
unpack(Bin)->
    try
	unpack_(Bin)
    catch
	error:Error when is_tuple(Error), element(1, Error) =:= error ->
	    Error;
	throw:Exception ->
	    {error, Exception}
    end.

-spec unpack_all( binary() ) -> [msgpack_term()].
unpack_all(Data)->
    case unpack(Data) of
	{ Term, Binary } when bit_size(Binary) =:= 0 ->
	    [Term];
	{ Term, Binary } when is_binary(Binary) ->
	    [Term|unpack_all(Binary)]
    end.

-spec pack_map(M::[{msgpack_term(),msgpack_term()}])-> binary() | {error, badarg}.
pack_map(M)->
    case length(M) of
	Len when Len < 16 ->
	    << 2#1000:4, Len:4/integer-unit:1, (pack_map_(M, <<>>))/binary >>;
	Len when Len < 16#10000 -> % 65536
	    << 16#DE:8, Len:16/big-unsigned-integer-unit:1, (pack_map_(M, <<>>))/binary >>;
	Len ->
	    << 16#DF:8, Len:32/big-unsigned-integer-unit:1, (pack_map_(M, <<>>))/binary >>
    end.

% ===== internal APIs ===== %

% pack them all
-spec pack_(msgpack_term()) -> binary() | no_return().
pack_(I) when is_integer(I) andalso I < 0 ->
    pack_int_(I);
pack_(I) when is_integer(I) ->
    pack_uint_(I);
pack_(F) when is_float(F) ->
    pack_double(F);
pack_(nil) ->
    << 16#C0:8 >>;
pack_(true) ->
    << 16#C3:8 >>;
pack_(false) ->
    << 16#C2:8 >>;
pack_(Bin) when is_binary(Bin) ->
    pack_raw(Bin);
pack_(List)  when is_list(List) ->
    pack_array(List);
pack_({Map}) when is_list(Map) ->
    pack_map(Map);
pack_(Map) when is_tuple(Map), element(1,Map)=:=dict ->
    pack_map(dict:to_list(Map));
pack_(_Other) ->
    throw({error, undefined}).

% positive fixnum
pack_uint_(N) when N < 128 ->
    << 2#0:1, N:7 >>;
% uint 8
pack_uint_(N) when N < 256 ->
    << 16#CC:8, N:8 >>;
% uint 16
pack_uint_(N) when N < 65536 ->
    << 16#CD:8, N:16/big-unsigned-integer-unit:1 >>;
% uint 32
pack_uint_(N) when N < 16#FFFFFFFF->
    << 16#CE:8, N:32/big-unsigned-integer-unit:1 >>;
% uint 64
pack_uint_(N) ->
    << 16#CF:8, N:64/big-unsigned-integer-unit:1 >>.

% negative fixnum
pack_int_(N) when is_integer(N) , N >= -32->
    << 2#111:3, N:5 >>;
% int 8
pack_int_(N) when N > -128 ->
    << 16#D0:8, N:8/big-signed-integer-unit:1 >>;
% int 16
pack_int_(N) when N > -32768 ->
    << 16#D1:8, N:16/big-signed-integer-unit:1 >>;
% int 32
pack_int_(N) when N > -16#FFFFFFFF ->
    << 16#D2:8, N:32/big-signed-integer-unit:1 >>;
% int 64
pack_int_(N) ->
    << 16#D3:8, N:64/big-signed-integer-unit:1 >>.

% float : erlang's float is always IEEE 754 64bit format.
% pack_float(F) when is_float(F)->
%    << 16#CA:8, F:32/big-float-unit:1 >>.
%    pack_double(F).
% double
pack_double(F) ->
    << 16#CB:8, F:64/big-float-unit:1 >>.

% raw bytes
pack_raw(Bin) ->
    case byte_size(Bin) of
	Len when Len < 6->
	    << 2#101:3, Len:5, Bin/binary >>;
	Len when Len < 16#10000 -> % 65536
	    << 16#DA:8, Len:16/big-unsigned-integer-unit:1, Bin/binary >>;
	Len ->
	    << 16#DB:8, Len:32/big-unsigned-integer-unit:1, Bin/binary >>
    end.

% list
pack_array(L) ->
    case length(L) of
 	Len when Len < 16 ->
 	    << 2#1001:4, Len:4/integer-unit:1, (pack_array_(L, <<>>))/binary >>;
	Len when Len < 16#10000 -> % 65536
	    << 16#DC:8, Len:16/big-unsigned-integer-unit:1,(pack_array_(L, <<>>))/binary >>;
	Len ->
	    << 16#DD:8, Len:32/big-unsigned-integer-unit:1,(pack_array_(L, <<>>))/binary >>
    end.

pack_array_([], Acc) -> Acc;
pack_array_([Head|Tail], Acc) ->
    pack_array_(Tail, <<Acc/binary,  (pack_(Head))/binary>>).

% Users SHOULD NOT send too long list: this uses lists:reverse/1
unpack_array_(Remain, 0,    Acc) when is_binary(Remain)-> {lists:reverse(Acc), Remain};
unpack_array_(<<>>, RestLen,  _) when RestLen > 0 -> throw(short);
unpack_array_(Bin, RestLen, Acc) when is_binary(Bin)->
    {Term, Rest}=unpack_(Bin),
    unpack_array_(Rest, RestLen-1, [Term|Acc]).

pack_map_([], Acc) -> Acc;
pack_map_([{Key,Value}|Tail], Acc) ->
    pack_map_(Tail, << Acc/binary, (pack_(Key))/binary, (pack_(Value))/binary>>).

% Users SHOULD NOT send too long list: this uses lists:reverse/1
-spec unpack_map_(binary(), non_neg_integer(), [{msgpack_term(), msgpack_term()}])->
			 {[{msgpack_term(), msgpack_term()}], binary()} | no_return().
unpack_map_(Bin,  0,  Acc) -> {{lists:reverse(Acc)}, Bin};
unpack_map_(<<>>, _,  _ )  -> throw(short);
unpack_map_(Bin, Len, Acc) ->
    {Key, Rest} = unpack_(Bin),
    {Value, Rest2} = unpack_(Rest),
    unpack_map_(Rest2,Len-1,[{Key,Value}|Acc]).

% unpack then all
-spec unpack_(Bin::binary()) -> {msgpack_term(), binary()} | {error, reason()} | no_return().
unpack_(Bin) when not is_binary(Bin)->    throw(badarg);
unpack_(Bin) when bit_size(Bin) >= 8 ->
    case Bin of
% ATOMS
	<<16#C0, Rest/binary>> -> {nil, Rest};
	<<16#C2, Rest/binary>> -> {false, Rest};
	<<16#C3, Rest/binary>> -> {true, Rest};
% Floats
	<<16#CA, V:32/float-unit:1, Rest/binary>> ->   {V, Rest};
	<<16#CB, V:64/float-unit:1, Rest/binary>> ->   {V, Rest};
% Unsigned integers
	<<16#CC, V:8/unsigned-integer, Rest/binary>> ->             {V, Rest};
	<<16#CD, V:16/big-unsigned-integer-unit:1, Rest/binary>> -> {V, Rest};
	<<16#CE, V:32/big-unsigned-integer-unit:1, Rest/binary>> -> {V, Rest};
	<<16#CF, V:64/big-unsigned-integer-unit:1, Rest/binary>> -> {V, Rest};
% Signed integers
	<<16#D0, V:8/signed-integer, Rest/binary>> ->             {V, Rest};
	<<16#D1, V:16/big-signed-integer-unit:1, Rest/binary>> -> {V, Rest};
	<<16#D2, V:32/big-signed-integer-unit:1, Rest/binary>> -> {V, Rest};
	<<16#D3, V:64/big-signed-integer-unit:1, Rest/binary>> -> {V, Rest};
% Raw bytes
	<<16#DA, L:16/unsigned-integer-unit:1, V:L/binary, Rest/binary>> -> {V, Rest};
	<<16#DB, L:32/unsigned-integer-unit:1, V:L/binary, Rest/binary>> -> {V, Rest};
% Arrays
	<<16#DC, L:16/big-unsigned-integer-unit:1, Rest/binary>> -> unpack_array_(Rest, L, []);
	<<16#DD, L:32/big-unsigned-integer-unit:1, Rest/binary>> -> unpack_array_(Rest, L, []);
% Maps
	<<16#DE, L:16/big-unsigned-integer-unit:1, Rest/binary>> -> unpack_map_(Rest, L, []);
	<<16#DF, L:32/big-unsigned-integer-unit:1, Rest/binary>> -> unpack_map_(Rest, L, []);

% Tag-encoded lengths (kept last, for speed)
	<<0:1, V:7, Rest/binary>> ->                 {V, Rest};                  % positive int
	<<2#111:3, V:5, Rest/binary>> ->             {V - 2#100000, Rest};       % negative int
	<<2#101:3, L:5, V:L/binary, Rest/binary>> -> {V, Rest};                  % raw bytes
	<<2#1001:4, L:4, Rest/binary>> ->            unpack_array_(Rest, L, []); % array
	<<2#1000:4, L:4, Rest/binary>> ->            unpack_map_(Rest, L, []);   % map
	
% Incomplete / invalid data
	<<F:16, _/binary>> when F==16#CA; F==16#CB; F==16#CC;
				F==16#CD; F==16#CE; F==16#CF;
				F==16#D0; F==16#D1; F==16#D2;
				F==16#D3; F==16#DA; F==16#DB;
				F==16#DC; F==16#DD; F==16#DE;
				F==16#DF ->
	    throw(short);
	<<F:16, _/binary>> when F==16#C1;
				F==16#C7; F==16#C8; F==16#C9;
				F==16#D5; F==16#D6; F==16#D7;
				F==16#D8; F==16#D9 ->
	    throw(badarg);
	_ ->
	    throw(short) % or unknown/badarg?
    end;
unpack_(<<>>)->                    throw(short);
unpack_(<<2#101:3, _/binary>>) ->  throw(short).

% ===== test codes ===== %
-include_lib("eunit/include/eunit.hrl").
-ifdef(EUNIT).

compare_all([], [])-> ok;
compare_all([],  R)-> {toomuchrhs, R};
compare_all(L,  [])-> {toomuchlhs, L};
compare_all([LH|LTL], [RH|RTL]) ->
    ?assertEqual(LH, RH),
    compare_all(LTL, RTL).

test_([]) -> 0;
test_([Term|Rest])->
    Pack = msgpack:pack(Term),
    ?assertEqual({Term, <<>>}, msgpack:unpack( Pack )),
    1+test_(Rest).

test_data()->
    [true, false, nil,
     0, 1, 2, 123, 512, 1230, 678908, 16#FFFFFFFFFF,
     -1, -23, -512, -1230, -567898, -16#FFFFFFFFFF,
     123.123, -234.4355, 1.0e-34, 1.0e64,
     [23, 234, 0.23],
     <<"hogehoge">>, <<"243546rf7g68h798j", 0, 23, 255>>,
     <<"hoasfdafdas][">>,
     [0,42, <<"sum">>, [1,2]], [1,42, nil, [3]],
     -234, -40000, -16#10000000, -16#100000000,
     42
    ].

basic_test()->
    Tests = test_data(),
    Passed = test_(Tests),
    Passed = length(Tests).

port_test()->
    Port = open_port({spawn, "ruby ../test/crosslang.rb"}, [binary]),
    Tests = test_data(),
    {[Tests],<<>>} = msgpack:unpack(msgpack:pack([Tests])),
    true = port_command(Port, msgpack:pack(Tests) ),
    receive
	{Port, {data, Data}}->  {Tests, <<>>}=msgpack:unpack(Data)
    after 1024-> ?assert(false)   end,
    port_close(Port).

test_p(Len,Term,OrigBin,Len) ->
    {Term, <<>>}=msgpack:unpack(OrigBin);
test_p(I,_,OrigBin,Len) when I < Len->
    <<Bin:I/binary, _/binary>> = OrigBin,
    ?assertEqual({error,short}, msgpack:unpack(Bin)).

partial_test()-> % error handling test.
    Term = lists:seq(0, 45),
    Bin=msgpack:pack(Term),
    BinLen = byte_size(Bin),
    [test_p(X, Term, Bin, BinLen) || X <- lists:seq(0,BinLen)].

long_test()->
    Longer = lists:seq(0, 655),
    {Longer, <<>>} = msgpack:unpack(msgpack:pack(Longer)).

map_test()->
    Ints = lists:seq(0, 65),
    Map = {[ {X, X*2} || X <- Ints ] ++ [{<<"hage">>, 324}, {43542, [nil, true, false]}]},
    {Map2, <<>>} = msgpack:unpack(msgpack:pack(Map)),
    ?assertEqual(Map, Map2),
    ok.

unknown_test()->
    Port = open_port({spawn, "ruby testcase_generator.rb"}, [binary]),
    Tests = [0, 1, 2, 123, 512, 1230, 678908,
	     -1, -23, -512, -1230, -567898,
	     <<"hogehoge">>, <<"243546rf7g68h798j">>,
	     123.123,
	     -234.4355, 1.0e-34, 1.0e64,
	     [23, 234, 0.23],
	     [0,42,<<"sum">>, [1,2]], [1,42, nil, [3]],
	     {[{1,2},{<<"hoge">>,nil}]}, % map
	     -234, -50000,
	     42
	    ],
    receive
	{Port, {data, Data}}-> compare_all(Tests, msgpack:unpack_all(Data))
    after 1024-> ?assert(false)  end,
    port_close(Port).

other_test()->
    ?assertEqual({error,short},msgpack:unpack(<<>>)).

benchmark_test()->
    Data=[test_data() || _ <- lists:seq(0, 10000)],
    S=?debugTime("  serialize", msgpack:pack(Data)),
    {Data,<<>>}=?debugTime("deserialize", msgpack:unpack(S)),
    ?debugFmt("for ~p KB test data.", [byte_size(S) div 1024]).

-endif.
