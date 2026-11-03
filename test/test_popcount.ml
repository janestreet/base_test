open! Import

module type%template [@alloc a @ m = (heap_global, stack_local)] T = sig
  type t [@@deriving (compare [@mode.explicit m]), quickcheck, (sexp_of [@alloc a])]

  (* for implementing popcount_naive *)

  val zero : t
  val one : t
  val ( + ) : t @ local -> t @ local -> t
  val ( lsr ) : t @ local -> int -> t
  val ( land ) : t @ local -> t @ local -> t
  val to_int_exn : t -> int
  val of_int_exn : int -> t
  val popcount : t -> t
end

module%template [@alloc a @ m = (heap_global, stack_local)] Make (Int : T [@alloc a]) =
struct
  let popcount_naive (int : Int.t) : int =
    let open Int in
    let rec loop n count =
      if (Int.compare [@mode m]) n zero <> 0
      then loop (n lsr 1) (count + (n land one))
      else count
    in
    loop int zero |> to_int_exn
  ;;

  let%test_unit _ =
    Base_quickcheck.Test.run_exn (module Int) ~f:(fun int ->
      let expect = popcount_naive int |> Int.of_int_exn in
      ([%test_result: Int.t] [@alloc a]) ~expect (Int.popcount int))
  ;;
end

include Make [@alloc stack] (struct
    include Int

    type t = int [@@deriving quickcheck]
  end)

include Make (struct
    include Int32

    type t = int32 [@@deriving quickcheck]
  end)

include Make (struct
    include Int64

    type t = int64 [@@deriving quickcheck]
  end)

include Make (struct
    include Nativeint

    type t = nativeint [@@deriving quickcheck]
  end)
