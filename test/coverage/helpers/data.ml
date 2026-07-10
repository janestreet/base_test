open! Base
open Base_quickcheck
open Overrides
include Data_intf.Definitions

module Int : S with type t = int = struct
  type t = int [@@deriving compare ~localize, equal ~localize, quickcheck, sexp_of]

  let to_int = Fn.id
  let of_int = Fn.id
  let combine_non_commutative a b = (a * 10) + b
end

module%template [@mode m = (local, global)] List (T : With_equal [@mode m]) = struct
  type t = T.t list [@@deriving (equal [@mode.explicit m]), sexp_of]
end

module%template [@mode m = (local, global)] Or_error (T : With_equal [@mode m]) = struct
  type t = (T.t, (Error.t[@equal.ignore])) Result.t
  [@@deriving (equal [@mode.explicit m]), sexp_of]
end

module%template [@mode m = (local, global)] Option (T : With_equal [@mode m]) = struct
  type t = T.t option [@@deriving (equal [@mode.explicit m]), sexp_of]
end

module%template [@mode m = (local, global)] Pair (T : With_quickcheck [@mode m]) = struct
  type t = T.t * T.t [@@deriving (equal [@mode.explicit m]), quickcheck, sexp_of]

  let quickcheck_generator =
    let open Base_quickcheck.Generator.Let_syntax in
    match%bind Base_quickcheck.Generator.bool with
    | true -> [%generator: t]
    | false ->
      let%map x = [%generator: T.t] in
      x, x
  ;;
end
