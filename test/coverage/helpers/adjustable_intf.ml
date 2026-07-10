open! Base

module Definitions = struct
  module type S = sig
    type t : value_or_null

    val get : t -> int
    val set : t -> int -> t
  end
end

module type Adjustable = sig
  include module type of struct
    include Definitions
  end

  val unique : ('a : value_or_null). (module S with type t = 'a) -> 'a -> 'a list -> 'a

  val non_overlapping
    : ('a : value_or_null).
    (module S with type t = 'a) -> 'a list -> 'a list
end
