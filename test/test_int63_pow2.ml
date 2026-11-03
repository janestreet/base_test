open! Import
open! Int63

module Expect_test_config = struct
  include Expect_test_config

  let sanitize string =
    let pattern =
      match Int63.Private.repr with
      | Int64 -> "Int64."
      | Int -> "Int."
    in
    String.substr_replace_all string ~pattern ~with_:"Int63."
  ;;
end

let examples = [ -1J; 0J; 1J; 2J; 3J; 4J; 5J; 7J; 8J; 9J; 63J; 64J; 65J ]
let examples_64_bit = [ min_value; succ min_value; pred max_value; max_value ]

let print_for ints f =
  List.iter ints ~f:(fun i ->
    print_s
      [%message
        "" ~_:(i : Int63.t) ~_:(Or_error.try_with (fun () -> f i) : Int63.t Or_error.t)])
;;

let%expect_test "[floor_log2]" =
  print_for examples floor_log2;
  [%expect
    {|
    (-1 (Error (Invalid_argument "Int63.floor_log2: -1")))
    (0 (Error (Invalid_argument "Int63.floor_log2: 0")))
    (1 (Ok 0))
    (2 (Ok 1))
    (3 (Ok 1))
    (4 (Ok 2))
    (5 (Ok 2))
    (7 (Ok 2))
    (8 (Ok 3))
    (9 (Ok 3))
    (63 (Ok 5))
    (64 (Ok 6))
    (65 (Ok 6))
    |}]
;;

let%expect_test "[floor_log2]" =
  print_for examples_64_bit floor_log2;
  [%expect
    {|
    (-4_611_686_018_427_387_904 (
      Error (Invalid_argument "Int63.floor_log2: -4611686018427387904")))
    (-4_611_686_018_427_387_903 (
      Error (Invalid_argument "Int63.floor_log2: -4611686018427387903")))
    (4_611_686_018_427_387_902 (Ok 61))
    (4_611_686_018_427_387_903 (Ok 61))
    |}]
;;

let%expect_test "[ceil_log2]" =
  print_for examples ceil_log2;
  [%expect
    {|
    (-1 (Error (Invalid_argument "Int63.ceil_log2: -1")))
    (0 (Error (Invalid_argument "Int63.ceil_log2: 0")))
    (1 (Ok 0))
    (2 (Ok 1))
    (3 (Ok 2))
    (4 (Ok 2))
    (5 (Ok 3))
    (7 (Ok 3))
    (8 (Ok 3))
    (9 (Ok 4))
    (63 (Ok 6))
    (64 (Ok 6))
    (65 (Ok 7))
    |}]
;;

let%expect_test "[ceil_log2]" =
  print_for examples_64_bit ceil_log2;
  [%expect
    {|
    (-4_611_686_018_427_387_904 (
      Error (Invalid_argument "Int63.ceil_log2: -4611686018427387904")))
    (-4_611_686_018_427_387_903 (
      Error (Invalid_argument "Int63.ceil_log2: -4611686018427387903")))
    (4_611_686_018_427_387_902 (Ok 62))
    (4_611_686_018_427_387_903 (Ok 62))
    |}]
;;

module%test [@name "int63_math"] _ = struct
  let test_cases () =
    let cases =
      [ 0b10101010J
      ; 0b1010101010101010J
      ; 0b101010101010101010101010J
      ; 0b10000000J
      ; 0b1000000000001000J
      ; 0b100000000000000000001000J
      ]
    in
    let cases =
      cases
      @ [ (0b1010101010101010J lsl 16) lor 0b1010101010101010J
        ; (0b1000000000000000J lsl 16) lor 0b0000000000001000J
        ]
    in
    let added_cases = List.map cases ~f:(fun x -> x lsl 16) in
    List.concat [ cases; added_cases ]
  ;;

  let%test_unit "ceil_pow2" =
    List.iter (test_cases ()) ~f:(fun x ->
      let p2 = ceil_pow2 x in
      assert (is_pow2 p2 && p2 >= x && x >= p2 / 2J))
  ;;

  let%test_unit "floor_pow2" =
    List.iter (test_cases ()) ~f:(fun x ->
      let p2 = floor_pow2 x in
      assert (is_pow2 p2 && 2J * p2 >= x && x >= p2))
  ;;
end
