open! Base
open Base_quickcheck
open Expect_test_helpers_base
open Generator.Let_syntax

open struct
  (* Testing helpers. Not part of [Enum]'s interface, so not exported. *)

  module Tree = Map.Tree
  module Enum = Tree.Enum

  let equal_enum =
    Comparable.lift
      [%equal: (int * int * (int, int, _) Tree.Expert.t) list]
      ~f:Enum.to_list_with_trees
  ;;

  let to_list_increasing (t : (_, _, _, Enum.increasing) Enum.t) =
    List.concat_map (Enum.to_list_with_trees t) ~f:(fun (key, data, tree) ->
      (key, data) :: Tree.to_alist tree)
  ;;

  let to_list_decreasing (t : (_, _, _, Enum.decreasing) Enum.t) =
    List.concat_map (Enum.to_list_with_trees t) ~f:(fun (key, data, tree) ->
      (key, data) :: List.rev (Tree.to_alist tree))
  ;;

  let pairs_gen =
    Generator.both
      Generator.small_strictly_positive_int
      Generator.small_strictly_positive_int
    |> Generator.list
    |> Generator.map ~f:(fun list ->
      List.dedup_and_sort list ~compare:[%compare: int * _] |> Iarray.of_list)
  ;;

  (* Custom generator to cover arbitrary internal structure of trees. *)
  let tree_of_pairs_gen pairs ~pos ~len =
    let rec loop ~pos ~len =
      match len with
      | 0 -> Generator.return Tree.Expert.empty
      | 1 ->
        let key, data = Iarray.get pairs pos in
        Generator.return (Tree.Expert.singleton key data)
      | _ ->
        (* Randomly balance between left and right. *)
        let%bind left_len = Generator.int_uniform_inclusive 0 (len - 1) in
        let%map left = loop ~pos ~len:left_len
        and right = loop ~pos:(pos + 1 + left_len) ~len:(len - left_len - 1) in
        let key, data = Iarray.get pairs (pos + left_len) in
        (* Rather than try to construct only valid left/right splits, we pick arbitrary
           ones, and anything unbalanced will be fixed up by this constructor. This is
           easier than trying to be super precise, and should still give us decent
           coverage. *)
        Tree.Expert.create_and_rebalance_unchecked left key data right
    in
    let%map.Generator tree = loop ~pos ~len in
    assert (
      [%equal: (int * int) iarray]
        (Iarray.of_list (Tree.to_alist tree))
        (Iarray.sub pairs ~pos ~len));
    tree
  ;;

  let tree_gen () =
    let%bind pairs = pairs_gen in
    tree_of_pairs_gen pairs ~pos:0 ~len:(Iarray.length pairs)
  ;;

  (* Custom generator to cover arbitrary internal structure of enums. *)
  let enum_increasing_of_pairs_gen pairs ~pos ~len =
    let rec loop ~pos ~len tail =
      match len with
      | 0 -> Generator.return tail
      | 1 ->
        let key, data = Iarray.get pairs pos in
        Generator.return ((key, data, Tree.Expert.empty) :: tail)
      | _ ->
        (* Choose where to split between [More] nodes. *)
        (match%bind Generator.int_uniform_inclusive 0 (len - 1) with
         | 0 ->
           (* Put everything in one node. *)
           let%map tree = tree_of_pairs_gen pairs ~pos:(pos + 1) ~len:(len - 1) in
           let key, data = Iarray.get pairs pos in
           (key, data, tree) :: tail
         | idx ->
           (* Put suffix in a final [More] node, recursively split up the prefix. *)
           let%bind tree =
             tree_of_pairs_gen pairs ~pos:(pos + idx + 1) ~len:(len - idx - 1)
           in
           let key, data = Iarray.get pairs (pos + idx) in
           loop ~pos ~len:idx ((key, data, tree) :: tail))
    in
    let%map.Generator list = loop ~pos ~len [] in
    let enum = Enum.of_list_with_trees list in
    assert (
      [%equal: (int * int) iarray]
        (Iarray.of_list (to_list_increasing enum))
        (Iarray.sub pairs ~pos ~len));
    enum
  ;;

  (* As above, for decreasing enums. The trees do not change internal order. *)
  let enum_decreasing_of_pairs_gen pairs ~pos ~len =
    let rec loop ~pos ~len tail =
      match len with
      | 0 -> Generator.return tail
      | 1 ->
        let key, data = Iarray.get pairs pos in
        Generator.return ((key, data, Tree.Expert.empty) :: tail)
      | _ ->
        (* Choose where to split between [More] nodes. *)
        (match%bind Generator.int_uniform_inclusive 0 (len - 1) with
         | 0 ->
           (* Put everything in one node. *)
           let%map tree = tree_of_pairs_gen pairs ~pos ~len:(len - 1) in
           let key, data = Iarray.get pairs (pos + len - 1) in
           (key, data, tree) :: tail
         | idx ->
           (* Put suffix in a final [More] node, recursively split up the prefix. *)
           let%bind tree = tree_of_pairs_gen pairs ~pos ~len:idx in
           let key, data = Iarray.get pairs (pos + idx) in
           loop ~pos:(pos + idx + 1) ~len:(len - idx - 1) ((key, data, tree) :: tail))
    in
    let%map.Generator list = loop ~pos ~len [] in
    let enum = Enum.of_list_with_trees list in
    assert (
      [%equal: (int * int) iarray]
        (Iarray.of_list_rev (to_list_decreasing enum))
        (Iarray.sub pairs ~pos ~len));
    enum
  ;;

  let enum_increasing_gen () =
    let%bind pairs = pairs_gen in
    enum_increasing_of_pairs_gen pairs ~pos:0 ~len:(Iarray.length pairs)
  ;;

  let enum_decreasing_gen () =
    let%bind pairs = pairs_gen in
    enum_decreasing_of_pairs_gen pairs ~pos:0 ~len:(Iarray.length pairs)
  ;;

  let tree_and_enum_increasing_gen () =
    let%bind pairs = pairs_gen in
    let len = Iarray.length pairs in
    let%bind idx = Generator.int_uniform_inclusive 0 len in
    let%bind tree = tree_of_pairs_gen pairs ~pos:0 ~len:idx in
    let%map enum = enum_increasing_of_pairs_gen pairs ~pos:idx ~len:(len - idx) in
    tree, enum
  ;;

  let tree_and_enum_decreasing_gen () =
    let%bind pairs = pairs_gen in
    let len = Iarray.length pairs in
    let%bind idx = Generator.int_uniform_inclusive 0 len in
    let%bind tree = tree_of_pairs_gen pairs ~pos:idx ~len:(len - idx) in
    let%map enum = enum_decreasing_of_pairs_gen pairs ~pos:0 ~len:idx in
    tree, enum
  ;;

  (* When generating pairs of trees and/or enums, half the time we generate one and modify
     it a bit on both sides, so that we test shared structure. *)

  let add_pairs_to_tree pairs tree =
    Iarray.fold pairs ~init:tree ~f:(fun acc (key, data) ->
      Map.Tree.set ~comparator:Int.comparator acc ~key ~data)
  ;;

  let rec add_to_enum_as_list enum_as_list ~key:k ~data:v =
    match enum_as_list with
    | [] -> [ k, v, Tree.Expert.empty ]
    | (key, data, tree) :: tail ->
      (match Int.compare k key with
       | c when c < 0 -> (k, v, Tree.Expert.empty) :: enum_as_list
       | c when c > 0 ->
         let tree, tail = add_to_tree_and_enum_as_list tree tail ~key:k ~data:v in
         (key, data, tree) :: tail
       | _ -> enum_as_list)

  and add_to_tree_and_enum_as_list tree enum_as_list ~key:k ~data:v =
    match enum_as_list with
    | (other, _, _) :: _ when Int.compare k other >= 0 ->
      tree, add_to_enum_as_list enum_as_list ~key:k ~data:v
    | _ -> Map.Tree.set ~comparator:Int.comparator tree ~key:k ~data:v, enum_as_list
  ;;

  let add_pairs_to_enum pairs enum =
    Iarray.fold pairs ~init:(Enum.to_list_with_trees enum) ~f:(fun acc (key, data) ->
      add_to_enum_as_list acc ~key ~data)
    |> Enum.of_list_with_trees
  ;;

  let pair_of_tree_gen () =
    Generator.union
      [ Generator.both (tree_gen ()) (tree_gen ())
      ; (let%map tree0 = tree_gen ()
         and pairs1 = pairs_gen
         and pairs2 = pairs_gen in
         add_pairs_to_tree pairs1 tree0, add_pairs_to_tree pairs2 tree0)
      ]
  ;;

  let pair_of_enum_increasing_gen () =
    Generator.union
      [ Generator.both (enum_increasing_gen ()) (enum_increasing_gen ())
      ; (let%map enum0 = enum_increasing_gen ()
         and pairs1 = pairs_gen
         and pairs2 = pairs_gen in
         add_pairs_to_enum pairs1 enum0, add_pairs_to_enum pairs2 enum0)
      ]
  ;;

  module Int_alist = struct
    type t = (int * int) list [@@deriving equal, sexp_of]
  end

  module Tree_and_enum_increasing = struct
    type nonrec t =
      (int, int, (Int.comparator_witness[@sexp.opaque])) Map.Tree.Expert.t
      * ( int
          , int
          , (Int.comparator_witness[@sexp.opaque])
          , (Enum.increasing[@sexp.opaque]) )
          Enum.t
    [@@deriving sexp_of]

    let quickcheck_generator = tree_and_enum_increasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Tree_and_enum_decreasing = struct
    type nonrec t =
      (int, int, (Int.comparator_witness[@sexp.opaque])) Map.Tree.Expert.t
      * ( int
          , int
          , (Int.comparator_witness[@sexp.opaque])
          , (Enum.decreasing[@sexp.opaque]) )
          Enum.t
    [@@deriving sexp_of]

    let quickcheck_generator = tree_and_enum_decreasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Tree_increasing = struct
    type t = (int, int, (Int.comparator_witness[@sexp.opaque])) Map.Tree.Expert.t
    [@@deriving sexp_of]

    let quickcheck_generator = tree_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Tree_and_key = struct
    type nonrec t =
      (int, int, (Int.comparator_witness[@sexp.opaque])) Map.Tree.Expert.t * int
    [@@deriving sexp_of]

    let quickcheck_generator =
      Generator.both (tree_gen ()) Generator.small_positive_or_zero_int
    ;;

    let quickcheck_shrinker = Shrinker.atomic
  end

  module Enum_increasing = struct
    type nonrec t =
      ( int
        , int
        , (Int.comparator_witness[@sexp.opaque])
        , (Enum.increasing[@sexp.opaque]) )
        Enum.t
    [@@deriving sexp_of]

    let equal = equal_enum
    let quickcheck_generator = enum_increasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Enum_decreasing = struct
    type nonrec t =
      ( int
        , int
        , (Int.comparator_witness[@sexp.opaque])
        , (Enum.decreasing[@sexp.opaque]) )
        Enum.t
    [@@deriving sexp_of]

    let quickcheck_generator = enum_decreasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Pair_of_tree = struct
    type nonrec t =
      (int, int, (Int.comparator_witness[@sexp.opaque])) Tree.Expert.t
      * (int, int, (Int.comparator_witness[@sexp.opaque])) Tree.Expert.t
    [@@deriving sexp_of]

    let quickcheck_generator = pair_of_tree_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Pair_of_enum = struct
    type nonrec t =
      ( int
        , int
        , (Int.comparator_witness[@sexp.opaque])
        , (Enum.increasing[@sexp.opaque]) )
        Enum.t
      * ( int
          , int
          , (Int.comparator_witness[@sexp.opaque])
          , (Enum.increasing[@sexp.opaque]) )
          Enum.t
    [@@deriving sexp_of]

    let quickcheck_generator = pair_of_enum_increasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end
end

(* Testing exports of [Enum]: *)

module Which = Enum.Which

type increasing = Enum.increasing
type decreasing = Enum.decreasing

type ('k, 'v, 'cmp, 'direction) nonempty = ('k, 'v, 'cmp, 'direction) Enum.nonempty

and ('k, 'v, 'cmp, 'direction) t = ('k, 'v, 'cmp, 'direction) nonempty or_null
[@@deriving sexp_of]

let to_list_with_trees = Enum.to_list_with_trees
let of_list_with_trees = Enum.of_list_with_trees

let%expect_test "to_list_with_trees / of_list_with_trees" =
  quickcheck_m (module Enum_increasing) ~f:(fun enum ->
    require_equal
      (module Enum_increasing)
      (Enum.of_list_with_trees (Enum.to_list_with_trees enum))
      enum)
;;

let length = Enum.length

let%expect_test "length" =
  quickcheck_m
    (module struct
      type nonrec t =
        (int, int, (Int.comparator_witness[@sexp.opaque]), (increasing[@sexp.opaque])) t
      [@@deriving sexp_of]

      let quickcheck_generator = enum_increasing_gen ()
      let quickcheck_shrinker = Shrinker.atomic
    end)
    ~f:(fun enum ->
      require_equal
        (module Int)
        (Enum.length enum)
        (List.length (to_list_increasing enum)))
;;

let key = Enum.key
let data = Enum.data
let next = Enum.next

let%expect_test "key & data & next" =
  quickcheck_m (module Enum_increasing) ~f:(fun enum ->
    require_equal
      (module Int_alist)
      (Sequence.unfold ~init:enum ~f:(fun enum ->
         match enum with
         | Null -> None
         | This enum -> Some ((Enum.key enum, Enum.data enum), Enum.next enum))
       |> Sequence.to_list)
      (List.concat_map (Enum.to_list_with_trees enum) ~f:(fun (k, v, tree) ->
         (k, v) :: Tree.to_alist tree)))
;;

let next_decreasing = Enum.next_decreasing

let%expect_test "key & data & next_decreasing" =
  quickcheck_m (module Enum_decreasing) ~f:(fun enum ->
    require_equal
      (module Int_alist)
      (Sequence.unfold ~init:enum ~f:(fun enum ->
         match enum with
         | Null -> None
         | This enum -> Some ((Enum.key enum, Enum.data enum), Enum.next_decreasing enum))
       |> Sequence.to_list)
      (List.concat_map (Enum.to_list_with_trees enum) ~f:(fun (k, v, tree) ->
         (k, v) :: Tree.to_alist tree ~key_order:`Decreasing)))
;;

let cons = Enum.cons

let%expect_test "cons" =
  quickcheck_m (module Tree_and_enum_increasing) ~f:(fun (tree, enum) ->
    require_equal
      (module Int_alist)
      (to_list_increasing (Enum.cons tree enum))
      (Map.Tree.to_alist tree @ to_list_increasing enum))
;;

let cons_right = Enum.cons_right

let%expect_test "cons_right" =
  quickcheck_m (module Tree_and_enum_decreasing) ~f:(fun (tree, enum) ->
    require_equal
      (module Int_alist)
      (to_list_decreasing (Enum.cons_right tree enum))
      (List.rev (Map.Tree.to_alist tree) @ to_list_decreasing enum));
  [%expect {| |}]
;;

let of_tree = Enum.of_tree

let%expect_test "of_tree" =
  quickcheck_m (module Tree_increasing) ~f:(fun tree ->
    require_equal
      (module Int_alist)
      (to_list_increasing (Enum.of_tree tree))
      (Map.Tree.to_alist tree))
;;

let of_tree_right = Enum.of_tree_right

let%expect_test "of_tree_right" =
  quickcheck_m (module Tree_increasing) ~f:(fun tree ->
    require_equal
      (module Int_alist)
      (to_list_decreasing (Enum.of_tree_right tree))
      (List.rev (Map.Tree.to_alist tree)));
  [%expect {| |}]
;;

let starting_at_increasing = Enum.starting_at_increasing

let%expect_test "starting_at_increasing" =
  quickcheck_m (module Tree_and_key) ~f:(fun (tree, pos) ->
    require_equal
      (module Int_alist)
      (to_list_increasing (Enum.starting_at_increasing tree pos Int.compare))
      (Sequence.to_list
         (Map.Tree.to_sequence
            tree
            ~comparator:Int.comparator
            ~order:`Increasing_key
            ~keys_greater_or_equal_to:pos)))
;;

let starting_at_decreasing = Enum.starting_at_decreasing

let%expect_test "starting_at_decreasing" =
  quickcheck_m (module Tree_and_key) ~f:(fun (tree, pos) ->
    require_equal
      (module Int_alist)
      (to_list_decreasing (Enum.starting_at_decreasing tree pos Int.compare))
      (Sequence.to_list
         (Map.Tree.to_sequence
            tree
            ~comparator:Int.comparator
            ~order:`Decreasing_key
            ~keys_less_or_equal_to:pos)));
  [%expect {| |}]
;;

let split_n = Enum.split_n

let%expect_test "split_n" =
  quickcheck_m
    (module struct
      type nonrec t =
        (int, int, (Int.comparator_witness[@sexp.opaque]), (increasing[@sexp.opaque])) t
        * int
      [@@deriving sexp_of]

      let quickcheck_generator =
        Generator.both (enum_increasing_gen ()) Generator.small_positive_or_zero_int
      ;;

      let quickcheck_shrinker = Shrinker.atomic
    end)
    ~f:(fun (enum, pos) ->
      let #(prefix, suffix) = Enum.split_n enum pos in
      require_equal
        (module Int)
        (Enum.length prefix)
        (Int.clamp_exn pos ~min:0 ~max:(Enum.length enum));
      require_equal
        (module struct
          type t = (int * int) list [@@deriving equal, sexp_of]
        end)
        (to_list_increasing prefix @ to_list_increasing suffix)
        (to_list_increasing enum))
;;

let which = Enum.which
let which_key = Enum.which_key
let which_merge_element = Enum.which_merge_element
let next2 = Enum.next2

let%expect_test "next2" =
  quickcheck_m (module Pair_of_enum) ~f:(fun (enum1, enum2) ->
    require_equal
      (module struct
        type t = (int * (int, int) Map.Merge_element.t) list [@@deriving equal, sexp_of]
      end)
      (Sequence.unfold ~init:(enum1, enum2) ~f:(fun (enum1, enum2) ->
         match enum1, enum2 with
         | Null, Null -> None
         | This enum1, Null ->
           Some ((Enum.key enum1, `Left (Enum.data enum1)), (Enum.next enum1, enum2))
         | Null, This enum2 ->
           Some ((Enum.key enum2, `Right (Enum.data enum2)), (enum1, Enum.next enum2))
         | This enum1, This enum2 ->
           let which = Enum.which enum1 enum2 ~compare_key:Int.compare in
           let k = Enum.which_key enum1 enum2 ~which in
           let v = Enum.which_merge_element enum1 enum2 ~which in
           let #(enum1, enum2) = Enum.next2 enum1 enum2 ~which in
           Some ((k, v), (enum1, enum2)))
       |> Sequence.to_list)
      (List.merge
         (to_list_increasing enum1 |> List.map ~f:(fun (k, v) -> k, `Left v))
         (to_list_increasing enum2 |> List.map ~f:(fun (k, v) -> k, `Right v))
         ~compare:(Comparable.lift Int.compare ~f:fst)
       |> List.fold_right ~init:[] ~f:(fun pair acc ->
         match pair, acc with
         | (k1, `Left v1), (k2, `Right v2) :: rest
         | (k2, `Right v2), (k1, `Left v1) :: rest
           when k1 = k2 -> (k1, `Both (v1, v2)) :: rest
         | _ -> pair :: acc)))
;;

let next2_drop_phys_equal = Enum.next2_drop_phys_equal

let%expect_test "next2 vs next2_drop_phys_equal" =
  quickcheck_m (module Pair_of_enum) ~f:(fun (enum1, enum2) ->
    let rec loop (enum1, enum2) (enum1_drop_phys_equal, enum2_drop_phys_equal) =
      match (enum1, enum2), (enum1_drop_phys_equal, enum2_drop_phys_equal) with
      | (Null, Null), (Null, Null) -> ()
      | ((This _ as a), Null), ((This _ as b), Null) -> require (equal_enum a b)
      | (Null, (This _ as a)), (Null, (This _ as b)) -> require (equal_enum a b)
      | (This enum1, This enum2), (This enum1_drop_phys_equal, This enum2_drop_phys_equal)
        ->
        (* Step using [next2] and [next2_drop_phys_equal], respectively. *)
        let whicha = which enum1 enum2 ~compare_key:Int.compare in
        let whichb =
          which enum1_drop_phys_equal enum2_drop_phys_equal ~compare_key:Int.compare
        in
        let ak = which_key enum1 enum2 ~which:whicha in
        let bk = which_key enum1_drop_phys_equal enum2_drop_phys_equal ~which:whichb in
        let avs = which_merge_element enum1 enum2 ~which:whicha in
        let bvs =
          which_merge_element enum1_drop_phys_equal enum2_drop_phys_equal ~which:whichb
        in
        let #(a1, a2) = next2 enum1 enum2 ~which:whicha in
        let #(b1, b2) =
          next2_drop_phys_equal enum1_drop_phys_equal enum2_drop_phys_equal ~which:whichb
        in
        (match avs, bvs with
         (* When [a]s match [b]s: *)
         | `Left av, `Left bv when ak = bk && av = bv -> loop (a1, a2) (b1, b2)
         | `Right av, `Right bv when ak = bk && av = bv -> loop (a1, a2) (b1, b2)
         | `Both (av1, av2), `Both (bv1, bv2) when ak = bk && av1 = bv1 && av2 = bv2 ->
           loop (a1, a2) (b1, b2)
         (* When [b]s dropped something [phys_equal], advance past it in [a]s: *)
         | `Both (av1, av2), _ when phys_equal av1 av2 ->
           loop (a1, a2) (This enum1_drop_phys_equal, This enum2_drop_phys_equal)
         (* Otherwise something is wrong: *)
         | _ ->
           print_cr
             [%message
               "different results"
                 (avs : (int, int) Map.Merge_element.t)
                 (bvs : (int, int) Map.Merge_element.t)])
      | _ ->
        (match
           (* Fix up when dropping [phys_equal] parts caused the outer match to fail *)
           match enum1, enum2 with
           | Null, _ | _, Null -> None
           | This enum1, This enum2 ->
             (match which enum1 enum2 ~compare_key:Int.compare with
              | Both as which when phys_equal (Enum.data enum1) (Enum.data enum2) ->
                let #(enum1, enum2) = Enum.next2 enum1 enum2 ~which in
                Some (enum1, enum2)
              | _ -> None)
         with
         | Some (enum1, enum2) ->
           loop (enum1, enum2) (enum1_drop_phys_equal, enum2_drop_phys_equal)
         | None ->
           (* Otherwise, again, something is wrong: *)
           print_cr
             [%message
               "different states"
                 (enum1 : (int, int, _, _) t)
                 (enum2 : (int, int, _, _) t)
                 (enum1_drop_phys_equal : (int, int, _, _) t)
                 (enum2_drop_phys_equal : (int, int, _, _) t)])
    in
    loop (enum1, enum2) (enum1, enum2));
  [%expect {| |}]
;;

let drop_phys_equal_prefix_of = Enum.drop_phys_equal_prefix_of

let%expect_test "drop_phys_equal_prefix" =
  quickcheck_m (module Pair_of_tree) ~f:(fun (tree1, tree2) ->
    let list1 = Tree.to_alist tree1 in
    let list2 = Tree.to_alist tree2 in
    let #(without_prefix1, without_prefix2) =
      Enum.drop_phys_equal_prefix_of tree1 tree2
    in
    let suffix1 = to_list_increasing without_prefix1 in
    let suffix2 = to_list_increasing without_prefix2 in
    let prefix1 = List.take list1 (List.length list1 - List.length suffix1) in
    let prefix2 = List.take list2 (List.length list2 - List.length suffix2) in
    let if_false_then_print_s =
      [%lazy_sexp
        { list1 : (int * int) list
        ; list2 : (int * int) list
        ; prefix1 : (int * int) list
        ; prefix2 : (int * int) list
        ; suffix1 : (int * int) list
        ; suffix2 : (int * int) list
        ; without_prefix1 : (int, int, _, _) t
        ; without_prefix2 : (int, int, _, _) t
        }]
    in
    require_equal
      (module Int_alist)
      prefix1
      prefix2
      ~message:"prefixes must be equal"
      ~if_false_then_print_s;
    require_equal
      (module Int_alist)
      list1
      (prefix1 @ suffix1)
      ~message:"first list must round-trip"
      ~if_false_then_print_s;
    require_equal
      (module Int_alist)
      list2
      (prefix2 @ suffix2)
      ~message:"second list must round-trip"
      ~if_false_then_print_s);
  [%expect {| |}]
;;

let split2 = Enum.split2

let%expect_test "split2" =
  let keys_of enums =
    List.concat_map enums ~f:to_list_increasing
    |> List.map ~f:fst
    |> List.dedup_and_sort ~compare:Int.compare
  in
  quickcheck_m
    (module struct
      type nonrec t =
        (int, int, (Int.comparator_witness[@sexp.opaque]), (increasing[@sexp.opaque])) t
        * (int, int, (Int.comparator_witness[@sexp.opaque]), (increasing[@sexp.opaque])) t
      [@@deriving sexp_of]

      let quickcheck_generator = pair_of_enum_increasing_gen ()
      let quickcheck_shrinker = Shrinker.atomic
    end)
    ~f:(fun (enum1, enum2) ->
      match Enum.split2 enum1 enum2 ~compare_key:Int.compare with
      | Null -> require (List.length (keys_of [ enum1; enum2 ]) < 2)
      | This (prefix1, prefix2, suffix1, suffix2) ->
        let if_false_then_print_s =
          [%lazy_sexp
            { prefix1 : (int, int, _, _) Enum.t
            ; prefix2 : (int, int, _, _) Enum.t
            ; suffix1 : (int, int, _, _) Enum.t
            ; suffix2 : (int, int, _, _) Enum.t
            }]
        in
        require (List.length (keys_of [ enum1; enum2 ]) >= 2) ~if_false_then_print_s;
        require (List.length (keys_of [ prefix1; prefix2 ]) >= 1) ~if_false_then_print_s;
        require (List.length (keys_of [ suffix1; suffix2 ]) >= 1) ~if_false_then_print_s;
        require
          (List.last_exn (keys_of [ prefix1; prefix2 ])
           < List.hd_exn (keys_of [ suffix1; suffix2 ]))
          ~if_false_then_print_s;
        let prefix_len = Enum.length prefix1 + Enum.length prefix2 in
        let suffix_len = Enum.length suffix1 + Enum.length suffix2 in
        require
          (prefix_len >= suffix_len / 3 && suffix_len >= prefix_len / 3)
          ~if_false_then_print_s;
        require_equal
          (module struct
            type t = (int * int) list [@@deriving equal, sexp_of]
          end)
          (to_list_increasing prefix1 @ to_list_increasing suffix1)
          (to_list_increasing enum1)
          ~if_false_then_print_s;
        require_equal
          (module struct
            type t = (int * int) list [@@deriving equal, sexp_of]
          end)
          (to_list_increasing prefix2 @ to_list_increasing suffix2)
          (to_list_increasing enum2)
          ~if_false_then_print_s);
  [%expect {| |}]
;;
