val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val plus : int -> int -> int

val mult : int -> int -> int

type positive =
  | XI of positive
  | XO of positive
  | XH

val psucc : positive -> positive

val pplus : positive -> positive -> positive

val pplus_carry : positive -> positive -> positive

val pmult_nat : positive -> int -> int

val nat_of_P : positive -> int

val p_of_succ_nat : int -> positive

val pmult : positive -> positive -> positive

type n =
  | N0
  | Npos of positive

val nplus : n -> n -> n

val nmult : n -> n -> n

val nat_of_N : n -> int

val n_of_nat : int -> n

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val eucl_dev : int -> int -> (int * int)

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val zero : ascii

val one : ascii

val shift : bool -> ascii -> ascii

val ascii_of_pos : positive -> ascii

val ascii_of_N : n -> ascii

val ascii_of_nat : int -> ascii

val n_of_digits : bool list -> n

val n_of_ascii : ascii -> n

val nat_of_ascii : ascii -> int

val take : int -> 'a1 list -> 'a1 list

val drop : int -> 'a1 list -> 'a1 list

val split_at : int -> 'a1 list -> 'a1 list * 'a1 list

val pair : 'a1 list -> ('a1 * 'a1) list

val pow : int -> int

val divmod : int -> int -> (int * int)

type ascii8 = ascii

type ascii16 = ascii8 * ascii8

type ascii32 = ascii16 * ascii16

type ascii64 = ascii32 * ascii32

val nat_of_ascii8 : ascii -> int

val ascii8_of_nat : int -> ascii

val ascii16_of_nat : int -> ascii * ascii

val nat_of_ascii16 : ascii16 -> int

val ascii32_of_nat : int -> (ascii * ascii) * (ascii * ascii)

val nat_of_ascii32 : ascii32 -> int

val list_of_ascii8 : ascii8 -> ascii8 list

val list_of_ascii16 : ascii16 -> ascii8 list

val list_of_ascii32 : ascii32 -> ascii8 list

val list_of_ascii64 : ascii64 -> ascii8 list

type object0 =
  | Bool of bool
  | Nil
  | PFixnum of ascii8
  | NFixnum of ascii8
  | Uint8 of ascii8
  | Uint16 of ascii16
  | Uint32 of ascii32
  | Uint64 of ascii64
  | Int8 of ascii8
  | Int16 of ascii16
  | Int32 of ascii32
  | Int64 of ascii64
  | Float of ascii32
  | Double of ascii64
  | FixRaw of ascii8 list
  | Raw16 of ascii8 list
  | Raw32 of ascii8 list
  | FixArray of object0 list
  | Array16 of object0 list
  | Array32 of object0 list
  | FixMap of (object0 * object0) list
  | Map16 of (object0 * object0) list
  | Map32 of (object0 * object0) list

val atat : ('a1 -> 'a2) -> 'a1 -> 'a2

val serialize : object0 -> ascii8 list

val compact : object0 list -> ascii8 list

val deserialize : int -> ascii8 list -> object0 list

