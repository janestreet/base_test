open! Base

module Definitions = struct
  module type%template [@mode m = (local, global)] With_compare = sig
    type t : value_or_null
    [@@deriving (compare [@mode.explicit m]), (equal [@mode.explicit m])]
  end
end

module type%template [@mode m = (local, global)] Func = sig
  include module type of struct
    include Definitions
  end

  type ('input : value_or_null, 'output : value_or_null) t =
    { initial : 'output
    ; transitions : ('input * 'output) list
    }
  [@@deriving (equal [@mode.explicit m]), quickcheck, sexp_of]

  val inputs : ('input, 'output) t -> 'input list
  val outputs : ('input, 'output) t -> 'output list

  val map
    : ('input1 : value_or_null) ('input2 : value_or_null) ('output1 : value_or_null)
      ('output2 : value_or_null).
    ('input1, 'output1) t
    -> i:('input1 -> 'input2)
    -> o:('output1 -> 'output2)
    -> ('input2, 'output2) t

  val apply
    : ('input : value_or_null) ('output : value_or_null).
    ('input, 'output) t -> (module With_compare with type t = 'input) -> 'input -> 'output

  val apply2
    : ('a : value_or_null) ('b : value_or_null) ('c : value_or_null).
    ('a, ('b, 'c) t) t
    -> (module With_compare with type t = 'a)
    -> (module With_compare with type t = 'b)
    -> 'a
    -> 'b
    -> 'c

  val apply3
    : ('a : value_or_null) ('b : value_or_null) ('c : value_or_null) ('d : value_or_null).
    ('a, ('b, ('c, 'd) t) t) t
    -> (module With_compare with type t = 'a)
    -> (module With_compare with type t = 'b)
    -> (module With_compare with type t = 'c)
    -> 'a
    -> 'b
    -> 'c
    -> 'd

  val injective
    : ('a : value_or_null) ('b : value_or_null).
    ('a, 'b) t
    -> (module With_compare with type t = 'a)
    -> (module Adjustable.S with type t = 'b)
    -> 'a list
    -> ('a, 'b) t
end
