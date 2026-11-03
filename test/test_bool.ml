open! Import
open! Expect_test_helpers_base

let%expect_test "hash coherence" =
  check_hash_coherence [%here] (module Bool) [ false; true ];
  [%expect {| |}]
;;

let%expect_test "Bool.Non_short_circuiting.(||)" =
  let ( || ) = Bool.Non_short_circuiting.( || ) in
  assert (true || true);
  assert (true || false);
  assert (false || true);
  assert (not (false || false));
  assert (
    true
    ||
    (print_endline "rhs";
     true));
  [%expect {| rhs |}];
  assert (
    false
    ||
    (print_endline "rhs";
     true));
  [%expect {| rhs |}]
;;

let%expect_test "Bool.Non_short_circuiting.(&&)" =
  let ( && ) = Bool.Non_short_circuiting.( && ) in
  assert (true && true);
  assert (not (true && false));
  assert (not (false && true));
  assert (not (false && false));
  assert (
    true
    &&
    (print_endline "rhs";
     true));
  [%expect {| rhs |}];
  assert (
    not
      (false
       &&
       (print_endline "rhs";
        true)));
  [%expect {| rhs |}]
;;

let%expect_test "[Bool.select]" =
  print_s [%sexp (Bool.select true 1 2 : int)];
  [%expect {| 1 |}];
  print_s [%sexp (Bool.select false 1 2 : int)];
  [%expect {| 2 |}];
  print_s [%sexp (Bool.select true "first" "second" : string)];
  [%expect {| first |}];
  print_s [%sexp (Bool.select false "first" "second" : string)];
  [%expect {| second |}];
  print_s [%sexp (Bool.select true 1.0 2.0 : float)];
  [%expect {| 1 |}];
  print_s [%sexp (Bool.select false 1.0 2.0 : float)];
  [%expect {| 2 |}];
  (* Both branches are evaluated *)
  let with_side_effect v =
    print_s [%message "Side effect" (v : int)];
    v
  in
  let (_ : int) = Bool.select true (with_side_effect 1) (with_side_effect 2) in
  [%expect
    {|
    ("Side effect" (v 2))
    ("Side effect" (v 1))
    |}];
  let (_ : int) = Bool.select false (with_side_effect 1) (with_side_effect 2) in
  [%expect
    {|
    ("Side effect" (v 2))
    ("Side effect" (v 1))
    |}]
;;

let%expect_test "[Bool.select] with [read] values" =
  let select if_ (then_ : int ref @ read uncontended) (else_ : int ref @ read uncontended)
    : int ref @ read uncontended
    =
    (Bool.select [@mode read]) if_ then_ else_
  in
  let consume (ref : int ref @ read uncontended) = print_s [%sexp (ref.contents : int)] in
  consume (select true (ref 1) (ref 2));
  [%expect {| 1 |}];
  consume (select false (ref 1) (ref 2));
  [%expect {| 2 |}]
;;

let%expect_test "[Bool.select] with [or_null] values" =
  print_s [%sexp (Bool.select true (This 1) Null : int or_null)];
  [%expect {| (1) |}];
  print_s [%sexp (Bool.select false (This 1) Null : int or_null)];
  [%expect {| () |}];
  print_s [%sexp (Bool.select true Null (This 2) : int or_null)];
  [%expect {| () |}];
  print_s [%sexp (Bool.select false Null (This 2) : int or_null)];
  [%expect {| (2) |}];
  print_s [%sexp (Bool.select true (This 1) (This 2) : int or_null)];
  [%expect {| (1) |}];
  print_s [%sexp (Bool.select false (This 1) (This 2) : int or_null)];
  [%expect {| (2) |}];
  print_s [%sexp (Bool.select true Null Null : int or_null)];
  [%expect {| () |}];
  print_s [%sexp (Bool.select false Null Null : int or_null)];
  [%expect {| () |}]
;;

let%expect_test "[Bool.select] on [value_or_null & bits64] products" =
  let print t = print_s [%sexp (t : #(int or_null * Int64_u.t))] in
  print ((Bool.select [@kind value_or_null & bits64]) true #(This 1, #10L) #(Null, #20L));
  [%expect {| ((1) 10) |}];
  print ((Bool.select [@kind value_or_null & bits64]) false #(This 1, #10L) #(Null, #20L));
  [%expect {| (() 20) |}]
;;
