open Base
open OUnit
open MsgpackCore
open Pack
open Printf

let c0 =
  Ascii (false,false,false,false,false,false,false,false)
let c1 =
  Ascii (true, false,false,false,false,false,false,false)
let c255 =
  Ascii (true,true,true,true,true,true,true,true)

let valid = [
  "nil",[
    Nil, `Nil
  ], [];
  "bool",[
    Bool true , `Bool true;
    Bool false, `Bool false
  ], [];
  "pfixnum",[
    PFixnum c0,`PFixnum 0;
    PFixnum c1,`PFixnum 1;
  ], [
    `PFixnum 128;
    `PFixnum (~-1);
  ];
  "nfixnum",[
    NFixnum c255, `NFixnum ~-1;
    NFixnum (Ascii (false,false,false,false,false,true,true,true)), `NFixnum ~-32
  ],[
    `NFixnum 0;
    `NFixnum (~-33)
  ];
  "uint8", [
    Uint8 c0, `Uint8 0;
    Uint8 c1, `Uint8 1;
    Uint8 c255, `Uint8 255
  ],[
    `Uint8 ~-1;
    `Uint8 256
  ];
  "uint16", [
    Uint16 (c0,c0), `Uint16 0;
    Uint16 (c0,c1), `Uint16 1;
    Uint16 (c1,c0), `Uint16 256;
    Uint16 (c255,c255), `Uint16 65535;
  ],[
    `Uint16 ~-1;
    `Uint16 65536
  ];
  "uint32", [
    Uint32 ((c0,c0), (c0,c0)), `Uint32 0L;
    Uint32 ((c255,c255), (c255,c255)), `Uint32 0xFFFF_FFFFL
  ],[
    `Uint32 (-1L);
    `Uint32 0x1FFFF_FFFFL
  ];
  "uint64", [
    Uint64 (((c0,c0), (c0,c0)),((c0,c0), (c0,c0))), `Uint64 Big_int.zero_big_int;
    Uint64 (((c0,c0), (c0,c0)),((c0,c0), (c0,c1))), `Uint64 Big_int.unit_big_int;
    Uint64 (((c255,c255), (c255,c255)),((c255,c255), (c255,c255))), `Uint64 (Big_int.big_int_of_string "18446744073709551615")
  ],[
    `Uint64 (Big_int.big_int_of_string "-1");
    `Uint64 (Big_int.big_int_of_string "18446744073709551617")
  ];
  "int8", [
    Int8 c0, `Int8 0;
    Int8 c1, `Int8 1;
    Int8 c255, `Int8 (~-1)
  ],[
    `Int8 129
  ];
  "int16", [
    Int16 (c0,c0), `Int16 0;
    Int16 (c0,c1), `Int16 1;
    Int16 (c1,c0), `Int16 256;
    Int16 (c255,c255), `Int16 ~-1;
  ],[
    `Int16 65536
  ];
  "int32", [
    Int32 ((c0,c0), (c0,c0)), `Int32 0l;
    Int32 ((c255,c255), (c255,c255)), `Int32 (-1l)
  ],[];
  "int64", [
    Int64 (((c0,c0), (c0,c0)),((c0,c0), (c0,c0))), `Int64 0L;
    Int64 (((c0,c0), (c0,c0)),((c0,c0), (c0,c1))), `Int64 1L;
    Int64 (((c255,c255), (c255,c255)),((c255,c255), (c255,c255))), `Int64 (-1L)
  ],[];
  "float", [
    Float ((c0,c0),(c0,c0)), `Float 0.0;
    (* 0.5 = 3f_00_00_00 *)
    Float ((Ascii (true,true,true,true,true,true,false,false),c0),(c0,c0)), `Float 0.5;
  ], [];
  "double", [
    Double (((c0,c0),(c0,c0)),((c0,c0),(c0,c0))), `Double 0.0;
    (* 0.5 = 3f_e0_00_00_00_00_00_00 *)
    Double (((Ascii (true,true,true,true,true,true,false,false),
	     Ascii (false,false,false,false,false,true,true,true)),
	     (c0,c0)),
	    ((c0,c0),(c0,c0))), `Double 0.5
  ],[];
  "fixraw", [
    FixRaw [], `FixRaw [];
    FixRaw [ c0 ], `FixRaw [ '\000'];
    FixRaw [ c0; c1 ], `FixRaw [ '\000'; '\001'];
  ],[];
  "raw16", [
    Raw16 [], `Raw16 [];
    Raw16 [ c0 ], `Raw16 [ '\000'];
    Raw16 [ c0; c1 ], `Raw16 [ '\000'; '\001'];
  ], [];
  "raw32", [
    Raw32 [], `Raw32 [];
    Raw32 [ c0 ], `Raw32 [ '\000'];
    Raw32 [ c0; c1 ], `Raw32 [ '\000'; '\001'];
  ], [];
  "fixarray", [
    FixArray [], `FixArray [];
    FixArray [ PFixnum c0 ], `FixArray [`PFixnum 0 ];
    FixArray [ FixArray [ PFixnum c0 ] ], `FixArray [`FixArray [ `PFixnum 0] ];
  ], [];
  "array16", [
    Array16 [], `Array16 [];
    Array16 [ PFixnum c0 ], `Array16 [`PFixnum 0 ];
    Array16 [ Array16 [ PFixnum c0 ] ], `Array16 [`Array16 [ `PFixnum 0] ];
  ], [];
  "array32", [
    Array32 [], `Array32 [];
    Array32 [ PFixnum c0 ], `Array32 [`PFixnum 0 ];
    Array32 [ Array32 [ PFixnum c0 ] ], `Array32 [`Array32 [ `PFixnum 0] ];
  ], [];
  "fixmap", [
    FixMap [], `FixMap [];
    FixMap [ PFixnum c0, PFixnum c1 ], `FixMap [`PFixnum 0, `PFixnum 1 ];
  ], [];
  "map16", [
    Map16 [], `Map16 [];
    Map16 [ PFixnum c0, PFixnum c1 ], `Map16 [`PFixnum 0, `PFixnum 1 ];
  ], [];
  "map32", [
    Map32 [], `Map32 [];
    Map32 [ PFixnum c0, PFixnum c1 ], `Map32 [`PFixnum 0, `PFixnum 1 ];
  ], [];
]


let _ = begin "pack.ml" >::: [
  "変換のテスト" >:::
    valid +> HList.concat_map begin fun (name, ok, ng) ->
       let xs =
	 ok +> List.map begin fun (expect, actual) ->
	   (sprintf "%sが変換できる" name) >:: (fun _ -> assert_equal expect (pack actual));
	 end in
       let ys =
	 ng +> List.map begin fun actual ->
	   (sprintf "%sのエラーチェック" name) >:: (fun _ -> assert_raises (Not_conversion name) (fun () -> pack actual))
	 end in
	 xs @ ys
    end;
  "復元のテスト" >:::
    valid +> HList.concat_map begin fun (name, ok, _) ->
      ok +> List.map begin fun (actual, expect) ->
	(sprintf "%sが復元できる" name) >:: begin fun _ ->
	  match expect, unpack actual with
	      `Uint64 n1, `Uint64 n2 ->
		assert_equal ~cmp:Big_int.eq_big_int n1 n2
	    | x, y ->
		assert_equal x y
	end
      end
    end;
] end +> run_test_tt_main
