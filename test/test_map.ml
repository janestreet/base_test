open! Import
open! Map

let%expect_test "Finished_or_unfinished <-> Continue_or_stop" =
  (* These functions are implemented using [Caml.Obj.magic]. It is important to test them
     comprehensively. *)
  List.iter2_exn Continue_or_stop.all Finished_or_unfinished.all ~f:(fun c_or_s f_or_u ->
    print_s [%sexp (c_or_s : Continue_or_stop.t), (f_or_u : Finished_or_unfinished.t)];
    require_equal
      (module Continue_or_stop)
      c_or_s
      (Finished_or_unfinished.to_continue_or_stop f_or_u);
    require_equal
      (module Finished_or_unfinished)
      f_or_u
      (Finished_or_unfinished.of_continue_or_stop c_or_s));
  [%expect
    {|
    (Continue Finished)
    (Stop Unfinished)
    |}]
;;

let%test _ =
  invariants (of_increasing_iterator_unchecked (module Int) ~len:20 ~f:(fun x -> x, x))
;;

let%test _ = invariants (Poly.of_increasing_iterator_unchecked ~len:20 ~f:(fun x -> x, x))
let add12 t = add_exn t ~key:1 ~data:2

type int_map = int Map.M(Int).t [@@deriving compare, hash, sexp]

let%expect_test "[add_exn] success" =
  print_s [%sexp (add12 (empty (module Int)) : int_map)];
  [%expect {| ((1 2)) |}]
;;

let%expect_test "[add_exn] failure" =
  show_raise (fun () -> add12 (add12 (empty (module Int))));
  [%expect {| (raised ("[Map.add_exn] got key already present" (key 1))) |}]
;;

let%expect_test "[add] success" =
  print_s [%sexp (add (empty (module Int)) ~key:1 ~data:2 : int_map Or_duplicate.t)];
  [%expect {| (Ok ((1 2))) |}]
;;

let%expect_test "[add] duplicate" =
  print_s
    [%sexp (add (add12 (empty (module Int))) ~key:1 ~data:2 : int_map Or_duplicate.t)];
  [%expect {| Duplicate |}]
;;

let%expect_test "[Map.of_alist_multi] preserves value ordering" =
  print_s
    [%sexp
      (Map.of_alist_multi (module String) [ "a", 1; "a", 2; "b", 1; "b", 3 ]
       : int list Map.M(String).t)];
  [%expect
    {|
    ((a (1 2))
     (b (1 3)))
    |}]
;;

let%expect_test "find_exn" =
  let map = Map.of_alist_exn (module String) [ "one", 1; "two", 2; "three", 3 ] in
  let test_success key =
    require_does_not_raise (fun () -> print_s [%sexp (Map.find_exn map key : int)])
  in
  test_success "one";
  [%expect {| 1 |}];
  test_success "two";
  [%expect {| 2 |}];
  test_success "three";
  [%expect {| 3 |}];
  let test_failure key =
    require_does_raise ~hide_positions:true (fun () -> Map.find_exn map key)
  in
  test_failure "zero";
  [%expect
    {| (Not_found_s ("Map.find_exn: not found" zero lib/base/test/test_map.ml:LINE:COL)) |}];
  test_failure "four";
  [%expect
    {| (Not_found_s ("Map.find_exn: not found" four lib/base/test/test_map.ml:LINE:COL)) |}]
;;

let%expect_test "[t_of_sexp] error on duplicate" =
  let sexp = Sexplib.Sexp.of_string "((0 a)(1 b)(2 c)(1 d))" in
  (match [%of_sexp: string Map.M(String).t] sexp with
   | t -> print_cr [%message "did not raise" (t : string Map.M(String).t)]
   | exception (Sexp.Of_sexp_error _ as exn) -> print_s (sexp_of_exn exn)
   | exception exn -> print_cr [%message "wrong kind of exception" (exn : exn)]);
  [%expect {| (Of_sexp_error "Map.t_of_sexp_direct: duplicate key" (invalid_sexp 1)) |}]
;;

let%expect_test "combine_errors" =
  let test list =
    let input =
      list
      |> List.map ~f:(Result.map_error ~f:Error.of_string)
      |> List.mapi ~f:(fun k x -> Int.succ k, x)
      |> Map.of_alist_exn (module Int)
    in
    let output = Map.combine_errors input in
    print_s [%sexp (output : string Map.M(Int).t Or_error.t)]
  in
  (* empty *)
  test [];
  [%expect {| (Ok ()) |}];
  (* singletons *)
  test [ Ok "one" ];
  test [ Error "one" ];
  [%expect
    {|
    (Ok ((1 one)))
    (Error ((1 one)))
    |}];
  (* multiple ok *)
  test [ Ok "one"; Ok "two"; Ok "three" ];
  [%expect
    {|
    (Ok (
      (1 one)
      (2 two)
      (3 three)))
    |}];
  (* multiple errors *)
  test [ Error "one"; Error "two"; Error "three" ];
  [%expect
    {|
    (Error (
      (1 one)
      (2 two)
      (3 three)))
    |}];
  (* one error among oks *)
  test [ Error "one"; Ok "two"; Ok "three" ];
  test [ Ok "one"; Error "two"; Ok "three" ];
  test [ Ok "one"; Ok "two"; Error "three" ];
  [%expect
    {|
    (Error ((1 one)))
    (Error ((2 two)))
    (Error ((3 three)))
    |}];
  (* one ok among errors *)
  test [ Ok "one"; Error "two"; Error "three" ];
  test [ Error "one"; Ok "two"; Error "three" ];
  test [ Error "one"; Error "two"; Ok "three" ];
  [%expect
    {|
    (Error (
      (2 two)
      (3 three)))
    (Error (
      (1 one)
      (3 three)))
    (Error (
      (1 one)
      (2 two)))
    |}]
;;

let%expect_test "[merge_aligned] passes correct keys and values to [~f]" =
  let map1 = Map.of_alist_exn (module Int) [ 1, 10; 2, 20; 3, 30; 4, 40 ] in
  let map2 = Map.of_alist_exn (module Int) [ 1, 1; 2, 2; 3, 3; 4, 4 ] in
  print_s
    [%sexp
      (Map.merge_aligned map1 map2 ~f:(fun ~key v1 v2 -> key, v1, v2)
       : (int * int * int) Map.M(Int).t Or_error.t)];
  [%expect
    {|
    (Ok (
      (1 (1 10 1))
      (2 (2 20 2))
      (3 (3 30 3))
      (4 (4 40 4))))
    |}]
;;

let%expect_test "[zip] / [zip_exn] on aligned maps" =
  let map1 = Map.of_alist_exn (module Int) [ 1, "a"; 2, "b"; 3, "c"; 4, "d" ] in
  let map2 = Map.of_alist_exn (module Int) [ 1, 1; 2, 2; 3, 3; 4, 4 ] in
  print_s [%sexp (Map.zip map1 map2 : (string * int) Map.M(Int).t Or_error.t)];
  [%expect
    {|
    (Ok (
      (1 (a 1))
      (2 (b 2))
      (3 (c 3))
      (4 (d 4))))
    |}];
  print_s [%sexp (Map.zip_exn map1 map2 : (string * int) Map.M(Int).t)];
  [%expect
    {|
    ((1 (a 1))
     (2 (b 2))
     (3 (c 3))
     (4 (d 4)))
    |}]
;;

let%expect_test "[merge_aligned] / [zip] / [zip_exn] error on mismatched keys" =
  let map1 = Map.of_alist_exn (module Int) [ 1, "a"; 2, "b" ] in
  let map2 = Map.of_alist_exn (module Int) [ 1, 1; 3, 3 ] in
  print_s [%sexp (Map.zip map1 map2 : (string * int) Map.M(Int).t Or_error.t)];
  [%expect
    {|
    (Error (
      "Map.zip: keys not aligned"
      ("only in first"  (2))
      ("only in second" (3))))
    |}];
  print_s
    [%sexp
      (Map.merge_aligned map1 map2 ~f:(fun ~key:_ _ _ -> ())
       : unit Map.M(Int).t Or_error.t)];
  [%expect
    {|
    (Error (
      "Map.merge_aligned: keys not aligned"
      ("only in first"  (2))
      ("only in second" (3))))
    |}];
  show_raise (fun () -> Map.zip_exn map1 map2);
  [%expect
    {|
    (raised (
      "Map.zip_exn: keys not aligned"
      ("only in first"  (2))
      ("only in second" (3))))
    |}]
;;

let%expect_test "[zip] error when one map is a strict superset of the other" =
  let map1 = Map.of_alist_exn (module Int) [ 1, "a"; 2, "b"; 3, "c" ] in
  let map2 = Map.of_alist_exn (module Int) [ 1, 1; 2, 2 ] in
  print_s [%sexp (Map.zip map1 map2 : (string * int) Map.M(Int).t Or_error.t)];
  [%expect
    {|
    (Error (
      "Map.zip: keys not aligned" ("only in first" (3)) ("only in second" ())))
    |}]
;;

let%expect_test "[zip] error when one map is empty and the other is not" =
  let map1 = Map.of_alist_exn (module Int) [ 1, "a" ] in
  let map2 = Map.empty (module Int) in
  print_s [%sexp (Map.zip map1 map2 : (string * int) Map.M(Int).t Or_error.t)];
  [%expect
    {|
    (Error (
      "Map.zip: keys not aligned" ("only in first" (1)) ("only in second" ())))
    |}]
;;

let%expect_test "[zip] / [merge_aligned] on two empty maps" =
  let map1 = Map.empty (module Int) in
  let map2 = Map.empty (module Int) in
  print_s [%sexp (Map.zip map1 map2 : (string * int) Map.M(Int).t Or_error.t)];
  [%expect {| (Ok ()) |}];
  print_s
    [%sexp
      (Map.merge_aligned map1 map2 ~f:(fun ~key:_ _ _ -> ())
       : unit Map.M(Int).t Or_error.t)];
  [%expect {| (Ok ()) |}]
;;

let%expect_test "[merge_aligned] sums aligned values" =
  let map1 = Map.of_alist_exn (module Int) [ 1, 1; 2, 2; 3, 3 ] in
  let map2 = Map.of_alist_exn (module Int) [ 1, 10; 2, 20; 3, 30 ] in
  print_s
    [%sexp
      (Map.merge_aligned map1 map2 ~f:(fun ~key:_ a b -> a + b)
       : int Map.M(Int).t Or_error.t)];
  [%expect
    {|
    (Ok (
      (1 11)
      (2 22)
      (3 33)))
    |}]
;;

module%test Poly = struct
  let%test _ = length Poly.empty = 0

  let%test _ =
    let a = Poly.of_alist_exn [] in
    Poly.equal Base.Poly.equal a Poly.empty
  ;;

  let%test _ =
    let a = Poly.of_alist_exn [ "a", 1 ] in
    let b = Poly.of_alist_exn [ 1, "b" ] in
    length a = length b
  ;;
end

module%test [@name "[symmetric_diff]"] _ = struct
  let%expect_test "examples" =
    let test alist1 alist2 =
      Map.symmetric_diff
        ~data_equal:Int.equal
        (Map.of_alist_exn (module String) alist1)
        (Map.of_alist_exn (module String) alist2)
      |> Sequence.to_list
      |> [%sexp_of: (string, int) Symmetric_diff_element.t list]
      |> print_s
    in
    test [] [];
    [%expect {| () |}];
    test [ "one", 1 ] [];
    [%expect {| ((one (Left 1))) |}];
    test [] [ "two", 2 ];
    [%expect {| ((two (Right 2))) |}];
    test [ "one", 1; "two", 2 ] [ "one", 1; "two", 2 ];
    [%expect {| () |}];
    test [ "one", 1; "two", 2 ] [ "one", 1; "two", 3 ];
    [%expect {| ((two (Unequal (2 3)))) |}]
  ;;

  module String_to_int_map = struct
    type t = int Map.M(String).t [@@deriving equal, sexp_of]

    open Base_quickcheck

    let quickcheck_generator =
      Generator.map_t_m (module String) Generator.string Generator.int
    ;;

    let quickcheck_observer = Observer.map_t Observer.string Observer.int
    let quickcheck_shrinker = Shrinker.map_t Shrinker.string Shrinker.int
  end

  let apply_diff_left_to_right map (key, elt) =
    match elt with
    | `Right data | `Unequal (_, data) -> Map.set map ~key ~data
    | `Left _ -> Map.remove map key
  ;;

  let apply_diff_right_to_left map (key, elt) =
    match elt with
    | `Left data | `Unequal (data, _) -> Map.set map ~key ~data
    | `Right _ -> Map.remove map key
  ;;

  (* This is a deterministic benchmark rather than a test, measuring the number of
     comparisons made by fold_symmetric_diff. *)
  let%expect_test "number of key comparisons" =
    let count = ref 0 in
    let measure_comparisons f =
      let c = !count in
      f ();
      !count - c
    in
    let module Key = struct
      type t = int [@@deriving sexp_of]

      let compare x y =
        Int.incr count;
        compare_int x y
      ;;

      include (val Comparator.make ~compare ~sexp_of_t)
    end
    in
    let test size =
      let map_pairs =
        (* We measure every step of building up a map from one side. This covers different
           stages of rebalancing along the way. *)
        List.folding_map
          (List.init size ~f:Int.succ)
          ~init:(Map.singleton (module Key) 0 0)
          ~f:(fun a i ->
            let b = Map.add_exn a ~key:i ~data:i in
            b, (a, b))
      in
      let add_comparisons = !count in
      count := 0;
      let comparisons =
        List.map map_pairs ~f:(fun (a, b) ->
          measure_comparisons (fun () ->
            Map.fold_symmetric_diff a b ~init:() ~f:(fun () _ -> ()) ~data_equal:( = )))
        |> List.sort ~compare:Int.compare
      in
      let len = List.length comparisons in
      let diff_comparisons = List.sum (module Int) comparisons ~f:Fn.id in
      let mean_diff_comparisons = Float.of_int diff_comparisons /. Float.of_int len in
      let median_diff_comparisons = List.nth_exn comparisons (len / 2) in
      let diff_comparison_buckets =
        List.sort_and_group comparisons ~compare:Int.compare
        |> List.map ~f:(fun list ->
          [%sexp
            { comparisons = (List.hd_exn list : int); times = (List.length list : int) }])
      in
      print_s
        [%message
          ""
            (size : int)
            (add_comparisons : int)
            (diff_comparisons : int)
            (mean_diff_comparisons : float)
            (median_diff_comparisons : int)
            (diff_comparison_buckets : Sexp.t list)]
    in
    test (1 lsl 20);
    [%expect
      {|
      ((size                    1_048_576)
       (add_comparisons         24_379_415)
       (diff_comparisons        4_194_035)
       (mean_diff_comparisons   3.9997434616088867)
       (median_diff_comparisons 3)
       (diff_comparison_buckets (
         ((comparisons 1)  (times 262_163))
         ((comparisons 3)  (times 262_145))
         ((comparisons 5)  (times 262_143))
         ((comparisons 6)  (times 131_071))
         ((comparisons 7)  (times 65_535))
         ((comparisons 8)  (times 32_767))
         ((comparisons 9)  (times 16_383))
         ((comparisons 10) (times 8_191))
         ((comparisons 11) (times 4_095))
         ((comparisons 12) (times 2_047))
         ((comparisons 13) (times 1_023))
         ((comparisons 14) (times 511))
         ((comparisons 15) (times 255))
         ((comparisons 16) (times 127))
         ((comparisons 17) (times 63))
         ((comparisons 18) (times 31))
         ((comparisons 19) (times 15))
         ((comparisons 20) (times 7))
         ((comparisons 21) (times 3))
         ((comparisons 22) (times 1)))))
      |}]
  ;;

  let%expect_test "reconstructing in both directions" =
    let test (map1, map2) =
      let diff = Map.symmetric_diff map1 map2 ~data_equal:Int.equal in
      require_equal
        (module String_to_int_map)
        (Sequence.fold diff ~init:map1 ~f:apply_diff_left_to_right)
        map2;
      require_equal
        (module String_to_int_map)
        map1
        (Sequence.fold diff ~init:map2 ~f:apply_diff_right_to_left)
    in
    Base_quickcheck.Test.run_exn
      ~f:test
      (module struct
        type t = String_to_int_map.t * String_to_int_map.t
        [@@deriving quickcheck, sexp_of]
      end)
  ;;

  let%expect_test "vs [fold_symmetric_diff]" =
    let test (map1, map2) =
      require_compare_equal
        (module struct
          type t = (string, int) Symmetric_diff_element.t list
          [@@deriving compare, sexp_of]
        end)
        (Map.symmetric_diff map1 map2 ~data_equal:Int.equal
         |> Sequence.fold ~init:[] ~f:(Fn.flip List.cons))
        (Map.fold_symmetric_diff
           map1
           map2
           ~data_equal:Int.equal
           ~init:[]
           ~f:(Fn.flip List.cons))
    in
    Base_quickcheck.Test.run_exn
      ~f:test
      (module struct
        type t = String_to_int_map.t * String_to_int_map.t
        [@@deriving quickcheck, sexp_of]
      end)
  ;;
end

module%test [@name "of_alist_multi key equality"] _ = struct
  module Key = struct
    module T = struct
      type t = string * int [@@deriving sexp_of]

      let compare = [%compare: string * _]
    end

    include T
    include Comparator.Make (T)
  end

  let alist = [ ("a", 1), 1; ("a", 2), 3; ("b", 0), 0; ("a", 3), 2 ]

  let%expect_test "of_alist_multi chooses the first key" =
    print_s [%sexp (Map.of_alist_multi (module Key) alist : int list Map.M(Key).t)];
    [%expect {| (((a 1) (1 3 2)) ((b 0) (0))) |}]
  ;;

  let%test_unit "of_{alist,sequence}_multi have the same behaviour" =
    [%test_result: int list Map.M(Key).t]
      ~expect:(Map.of_alist_multi (module Key) alist)
      (Map.of_sequence_multi (module Key) (Sequence.of_list alist))
  ;;
end

let%expect_test "remove returns the same object if there's nothing to do" =
  let map1 = Map.of_alist_exn (module Int) [ 1, "one"; 3, "three" ] in
  let map2 = Map.remove map1 2 in
  require (phys_equal map1 map2)
;;

let%expect_test "[map_keys]" =
  let test m c ~f =
    print_s
      [%sexp
        (Map.map_keys c ~f m
         : [ `Duplicate_key of string | `Ok of string Map.M(String).t ])]
  in
  let map = Map.of_alist_exn (module Int) [ 1, "one"; 2, "two"; 3, "three" ] in
  test map (module String) ~f:Int.to_string;
  [%expect
    {|
    (Ok (
      (1 one)
      (2 two)
      (3 three)))
    |}];
  test map (module String) ~f:(fun x -> Int.to_string (x / 2));
  [%expect {| (Duplicate_key 1) |}]
;;

let%expect_test "[fold_until]" =
  let test t =
    print_s
      [%sexp
        (Map.fold_until
           t
           ~init:0
           ~f:(fun ~key ~data acc -> if key > 2 then Stop data else Continue (acc + key))
           ~finish:Int.to_string
         : string)]
  in
  let map = Map.of_alist_exn (module Int) [ 1, "one"; 2, "two"; 3, "three" ] in
  test map;
  [%expect {| three |}];
  let map = Map.of_alist_exn (module Int) [ -1, "minus-one"; 1, "one"; 2, "two" ] in
  test map;
  [%expect {| 2 |}]
;;

let%expect_test "[sum]" =
  let test t = print_s [%sexp (Map.sum (module Int) t ~f:(( * ) 2) : int)] in
  let map = Map.of_alist_exn (module String) [ "A", 1; "B", 2; "C", 3 ] in
  test map;
  [%expect {| 12 |}]
;;

let%expect_test "[sumi]" =
  let test t =
    print_s [%sexp (Map.sumi (module Int) t ~f:(fun ~key ~data -> key * data) : int)]
  in
  let map = Map.of_alist_exn (module Int) [ 1, 1; 2, 2; 3, 3 ] in
  test map;
  [%expect {| 14 |}]
;;

let%expect_test "[merge_disjoint_exn] success" =
  let map1 = Map.of_alist_exn (module Int) [ 1, "one"; 2, "two" ] in
  let map2 = Map.of_alist_exn (module Int) [ 3, "three" ] in
  print_s [%sexp (Map.merge_disjoint_exn map1 map2 : string Map.M(Int).t)];
  [%expect
    {|
    ((1 one)
     (2 two)
     (3 three))
    |}]
;;

let%expect_test "[merge_disjoint_exn] failure" =
  let map1 = Map.of_alist_exn (module Int) [ 1, "one"; 2, "two" ] in
  let map2 = Map.of_alist_exn (module Int) [ 2, "two"; 3, "three" ] in
  show_raise (fun () -> Map.merge_disjoint_exn map1 map2);
  [%expect {| (raised ("Map.merge_disjoint_exn: duplicate key" 2)) |}]
;;

let create_balanced array = Map.of_sorted_array_unchecked (module Int) array

let create_left_to_right array =
  Array.fold
    array
    ~init:(Map.empty (module Int))
    ~f:(fun map (key, data) -> Map.add_exn map ~key ~data)
;;

let create_right_to_left array =
  Array.fold_right
    array
    ~init:(Map.empty (module Int))
    ~f:(fun (key, data) map -> Map.add_exn map ~key ~data)
;;

let create_random array =
  Array.permute ~random_state:(Random.State.make [| Array.length array |]) array;
  create_left_to_right array
;;

(* This is flaky depending on runtime details. *)
let%expect_test ("space" [@tags "no-js", "disabled"]) =
  let create ~length ~construction =
    let array = Array.init length ~f:(fun x -> x + 1, x + 1) in
    match construction with
    | `l_to_r -> create_left_to_right array
    | `r_to_l -> create_right_to_left array
    | `balanced -> create_balanced array
    | `random -> create_random array
  in
  let sexps =
    let%bind.List length = [ 1; 100; 10_000; 1_000_000 ] in
    let%map.List construction = [ `l_to_r; `r_to_l; `balanced; `random ] in
    let t = create ~length ~construction in
    let words = Stdlib.Obj.reachable_words (Stdlib.Obj.repr t) in
    [%sexp
      { length : int
      ; construction : [ `l_to_r | `r_to_l | `balanced | `random ]
      ; words : int
      }]
  in
  Expectable.print sexps;
  [%expect
    {|
    ┌───────────┬──────────────┬───────────┐
    │ length    │ construction │ words     │
    ├───────────┼──────────────┼───────────┤
    │         1 │ l_to_r       │        33 │
    │         1 │ r_to_l       │        33 │
    │         1 │ balanced     │        33 │
    │         1 │ random       │        33 │
    │       100 │ l_to_r       │       480 │
    │       100 │ r_to_l       │       480 │
    │       100 │ balanced     │       519 │
    │       100 │ random       │       504 │
    │    10_000 │ l_to_r       │    45_030 │
    │    10_000 │ r_to_l       │    45_030 │
    │    10_000 │ balanced     │    47_742 │
    │    10_000 │ random       │    47_100 │
    │ 1_000_000 │ l_to_r       │ 4_500_030 │
    │ 1_000_000 │ r_to_l       │ 4_500_030 │
    │ 1_000_000 │ balanced     │ 4_572_891 │
    │ 1_000_000 │ random       │ 4_714_581 │
    └───────────┴──────────────┴───────────┘
    |}]
;;
