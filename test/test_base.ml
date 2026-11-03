open! Import

let%expect_test _ =
  let f x = x * 2 in
  let g x = x + 3 in
  print_s [%sexp (f @@ 5 : int)];
  [%expect {| 10 |}];
  print_s [%sexp (g @@ f @@ 5 : int)];
  [%expect {| 13 |}];
  print_s [%sexp (f @@ g @@ 5 : int)];
  [%expect {| 16 |}]
;;

let%expect_test "exp is present at the toplevel" =
  print_s [%sexp (2 ** 8 : int)];
  [%expect {| 256 |}]
;;

[%%test
  module _ =
    [%template
    include (
    struct
      type t = int [@@kind immediate]
      and t = Basement.Nativeint_u.t [@@kind word]
      and t = Basement.Int32_u.t [@@kind bits32]
      and t = Basement.Int64_u.t [@@kind bits64]
      and t = float# [@@kind float64]

      let zero () = 0 [@@kind immediate]
      and zero () = #0n [@@kind word]
      and zero () = #0l [@@kind bits32]
      and zero () = #0L [@@kind bits64]
      and zero () = #0. [@@kind float64]

      let is_zero = function
        | 0 -> true
        | _ -> false
      [@@kind immediate]

      and is_zero = function
        | #0n -> true
        | _ -> false
      [@@kind word]

      and is_zero = function
        | #0l -> true
        | _ -> false
      [@@kind bits32]

      and is_zero = function
        | #0L -> true
        | _ -> false
      [@@kind bits64]

      and is_zero = function
        | #0. -> true
        | _ -> false
      [@@kind float64]
      ;;
    end :
    sig
      [@@@kind.default k = (immediate, word, bits32, bits64, float64)]

      type t : k

      val zero : unit -> (t[@kind k])
      val is_zero : (t[@kind k]) -> bool
    end)

    [@@@kind k = (immediate, word, bits32, bits64, float64)]

    [%%test_unit let "ignore" = ignore ((zero [@kind k]) () : (t[@kind k]))]

    [%%test
      let "apply/revapply identity" = Fn.id @@ (zero [@kind k]) () |> (is_zero [@kind k])]

    [%%test
      let "apply/revapply opaque" =
        Sys.opaque_identity @@ (zero [@kind k]) () |> (is_zero [@kind k])
      ;;]]
  [@@name "layout polymorphism"]]
