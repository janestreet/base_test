open! Base

module Definitions = struct
  module type%template [@mode m = (local, global)] S = sig
    type t
    [@@deriving
      (compare [@mode.explicit m]), (equal [@mode.explicit m]), quickcheck, sexp_of]

    val to_int : t -> int
    val of_int : int -> t
    val combine_non_commutative : t -> t -> t
  end

  module type%template [@mode m = (local, global)] With_equal = sig
    type t [@@deriving (equal [@mode.explicit m]), sexp_of]
  end

  module type%template [@mode m = (local, global)] With_quickcheck = sig
    type t [@@deriving (equal [@mode.explicit m]), quickcheck, sexp_of]
  end
end

module type Data = sig
  include module type of struct
    include Definitions
  end

  module Int : S with type t = int

  (** Functor for [List] *)
  module%template [@mode m = (local, global)] List (T : With_equal [@mode m]) :
    With_equal with type t = T.t list

  (** Functor for [Or_error], ignoring error contents when comparing. *)
  module%template [@mode m = (local, global)] Or_error (T : With_equal [@mode m]) :
    With_equal with type t = T.t Or_error.t

  (** Functor for [Option] *)
  module%template [@mode m = (local, global)] Option (T : With_equal [@mode m]) :
    With_equal with type t = T.t option

  (** Functor for pairs of the same data, with quickcheck generation. *)
  module%template [@mode m = (local, global)] Pair (T : With_quickcheck [@mode m]) :
    With_quickcheck with type t = T.t * T.t
end
