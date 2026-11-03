open! Import
open! Ppx_compare_lib

module Unit = struct
  type t = unit [@@deriving compare ~localize, sexp_of]
end

module type%template [@mode m = (global, local)] T = sig
  type t [@@deriving (compare [@mode.explicit m]), sexp_of]
end

let%template[@mode m = (global, local)] test
  (type a)
  (module T : T with type t = a[@mode m])
  ordered
  =
  List.iteri ordered ~f:(fun i ti ->
    List.iteri ordered ~f:(fun j tj ->
      require
        (Ordering.equal
           (Ordering.of_int ((T.compare [@mode m]) ti tj))
           (Ordering.of_int (Int.compare i j)))
        ~if_false_then_print_s:(lazy [%message "" ~_:(ti : T.t) ~_:(tj : T.t)])))
;;

let%expect_test "bool, char, unit" =
  (test [@mode local]) (module Bool) [ false; true ];
  test (module Char) [ '\000'; 'a'; 'b' ];
  [%expect {| |}];
  test (module Unit) [ () ];
  [%expect {| |}]
;;

module type%template [@mode m = (global, local)] Min_zero_max = sig
  include T [@mode m]

  val min_value : t
  val max_value : t
  val zero : t
end

let%template[@mode m = (global, local)] test_min_zero_max
  (type a)
  (module T : Min_zero_max with type t = a[@mode m])
  =
  (test [@mode m]) (module T) [ T.min_value; T.zero; T.max_value ]
;;

let%expect_test _ =
  (test_min_zero_max [@mode local]) (module Float);
  test_min_zero_max (module Int);
  test_min_zero_max (module Int32);
  test_min_zero_max (module Int64);
  test_min_zero_max (module Nativeint)
;;

let%expect_test "option" =
  test
    (module struct
      type t = int option [@@deriving compare ~localize, sexp_of]
    end)
    [ None; Some 0; Some 1 ]
;;

let%expect_test "ref" =
  test
    (module struct
      type t = int ref [@@deriving compare ~localize, sexp_of]
    end)
    ([ -1; 0; 1 ] |> List.map ~f:ref)
;;

module type%template [@mode m = (global, local)] Sequence = sig
  type 'a t [@@deriving (compare [@mode.explicit m]), sexp_of]

  val of_list : 'a list -> 'a t
end

let%template[@mode m = (global, local)] test_sequence
  (module T : Sequence[@mode m])
  ordered
  =
  (test [@mode m])
    (module struct
      type t = int T.t [@@deriving (compare [@mode.explicit m]), sexp_of]
    end)
    (ordered |> List.map ~f:T.of_list)
;;

let%expect_test "array, list" =
  (test_sequence [@mode local]) (module Array) [ []; [ 1 ]; [ 2 ]; [ 1; 2 ]; [ 2; 1 ] ];
  test_sequence (module List) [ []; [ 1 ]; [ 1; 2 ]; [ 2 ]; [ 2; 1 ] ]
;;

let%expect_test "[compare_abstract]" =
  show_raise (fun () -> compare_abstract ~type_name:"TY" () ());
  [%expect
    {|
    (raised (
      Failure
      "Compare called on the type TY, which is abstract in an implementation."))
    |}]
;;
