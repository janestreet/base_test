open! Base
open Base_quickcheck
open Expect_test_helpers_base
open Generator.Let_syntax

open struct
  (* Testing helpers. Not part of [Enum]'s interface, so not exported. *)

  module Tree = Set.Tree
  module Enum = Tree.Enum

  let equal_enum =
    Comparable.lift
      [%equal: (int * (int, _) Tree.Expert.t) list]
      ~f:Enum.to_list_with_trees
  ;;

  let to_list_increasing (t : (_, _, Enum.increasing) Enum.t) =
    List.concat_map (Enum.to_list_with_trees t) ~f:(fun (elt, tree) ->
      elt :: Tree.to_list tree)
  ;;

  let to_list_decreasing (t : (_, _, Enum.decreasing) Enum.t) =
    List.concat_map (Enum.to_list_with_trees t) ~f:(fun (elt, tree) ->
      elt :: List.rev (Tree.to_list tree))
  ;;

  let elts_gen =
    Generator.small_strictly_positive_int
    |> Generator.list
    |> Generator.map ~f:(fun list ->
      List.dedup_and_sort list ~compare:[%compare: int] |> Iarray.of_list)
  ;;

  (* Custom generator to cover arbitrary internal structure of trees. *)
  let tree_of_elts_gen elts ~pos ~len =
    let rec loop ~pos ~len =
      match len with
      | 0 -> Generator.return Tree.Expert.empty
      | 1 ->
        let elt = Iarray.get elts pos in
        Generator.return (Tree.Expert.singleton elt)
      | _ ->
        (* Randomly balance between left and right. *)
        let%bind left_len = Generator.int_uniform_inclusive 0 (len - 1) in
        let%map left = loop ~pos ~len:left_len
        and right = loop ~pos:(pos + 1 + left_len) ~len:(len - left_len - 1) in
        let elt = Iarray.get elts (pos + left_len) in
        (* Rather than try to construct only valid left/right splits, we pick arbitrary
           ones, and anything unbalanced will be fixed up by this constructor. This is
           easier than trying to be super precise, and should still give us decent
           coverage. *)
        Tree.Expert.create_and_rebalance_unchecked left elt right
    in
    let%map.Generator tree = loop ~pos ~len in
    assert (
      [%equal: int iarray]
        (Iarray.of_list (Tree.to_list tree))
        (Iarray.sub elts ~pos ~len));
    tree
  ;;

  let tree_gen () =
    let%bind elts = elts_gen in
    tree_of_elts_gen elts ~pos:0 ~len:(Iarray.length elts)
  ;;

  (* Custom generator to cover arbitrary internal structure of enums. *)
  let enum_increasing_of_elts_gen elts ~pos ~len =
    let rec loop ~pos ~len tail =
      match len with
      | 0 -> Generator.return tail
      | 1 -> Generator.return ((Iarray.get elts pos, Tree.Expert.empty) :: tail)
      | _ ->
        (* Choose where to split between [More] nodes. *)
        (match%bind Generator.int_uniform_inclusive 0 (len - 1) with
         | 0 ->
           (* Put everything in one node. *)
           let%map tree = tree_of_elts_gen elts ~pos:(pos + 1) ~len:(len - 1) in
           (Iarray.get elts pos, tree) :: tail
         | idx ->
           (* Put suffix in a final [More] node, recursively split up the prefix. *)
           let%bind tree =
             tree_of_elts_gen elts ~pos:(pos + idx + 1) ~len:(len - idx - 1)
           in
           loop ~pos ~len:idx ((Iarray.get elts (pos + idx), tree) :: tail))
    in
    let%map.Generator list = loop ~pos ~len [] in
    let enum = Enum.of_list_with_trees list in
    assert (
      [%equal: int iarray]
        (Iarray.of_list (to_list_increasing enum))
        (Iarray.sub elts ~pos ~len));
    enum
  ;;

  (* As above, for decreasing enums. The trees do not change internal order. *)
  let enum_decreasing_of_elts_gen elts ~pos ~len =
    let rec loop ~pos ~len tail =
      match len with
      | 0 -> Generator.return tail
      | 1 -> Generator.return ((Iarray.get elts pos, Tree.Expert.empty) :: tail)
      | _ ->
        (* Choose where to split between [More] nodes. *)
        (match%bind Generator.int_uniform_inclusive 0 (len - 1) with
         | 0 ->
           (* Put everything in one node. *)
           let%map tree = tree_of_elts_gen elts ~pos ~len:(len - 1) in
           (Iarray.get elts (pos + len - 1), tree) :: tail
         | idx ->
           (* Put suffix in a final [More] node, recursively split up the prefix. *)
           let%bind tree = tree_of_elts_gen elts ~pos ~len:idx in
           loop
             ~pos:(pos + idx + 1)
             ~len:(len - idx - 1)
             ((Iarray.get elts (pos + idx), tree) :: tail))
    in
    let%map.Generator list = loop ~pos ~len [] in
    let enum = Enum.of_list_with_trees list in
    assert (
      [%equal: int iarray]
        (Iarray.of_list_rev (to_list_decreasing enum))
        (Iarray.sub elts ~pos ~len));
    enum
  ;;

  let enum_increasing_gen () =
    let%bind elts = elts_gen in
    enum_increasing_of_elts_gen elts ~pos:0 ~len:(Iarray.length elts)
  ;;

  let enum_decreasing_gen () =
    let%bind elts = elts_gen in
    enum_decreasing_of_elts_gen elts ~pos:0 ~len:(Iarray.length elts)
  ;;

  let tree_and_enum_increasing_gen () =
    let%bind elts = elts_gen in
    let len = Iarray.length elts in
    let%bind idx = Generator.int_uniform_inclusive 0 len in
    let%bind tree = tree_of_elts_gen elts ~pos:0 ~len:idx in
    let%map enum = enum_increasing_of_elts_gen elts ~pos:idx ~len:(len - idx) in
    tree, enum
  ;;

  let tree_and_enum_decreasing_gen () =
    let%bind elts = elts_gen in
    let len = Iarray.length elts in
    let%bind idx = Generator.int_uniform_inclusive 0 len in
    let%bind tree = tree_of_elts_gen elts ~pos:idx ~len:(len - idx) in
    let%map enum = enum_decreasing_of_elts_gen elts ~pos:0 ~len:idx in
    tree, enum
  ;;

  let rec add_to_enum_as_list enum_as_list x =
    match enum_as_list with
    | [] -> [ x, Tree.Expert.empty ]
    | (elt, tree) :: tail ->
      (match Int.compare x elt with
       | c when c < 0 -> (x, Tree.Expert.empty) :: enum_as_list
       | c when c > 0 ->
         (match tail with
          | (other, _) :: _ when Int.compare x other >= 0 ->
            (elt, tree) :: add_to_enum_as_list tail x
          | _ -> (elt, Set.Tree.add ~comparator:Int.comparator tree x) :: tail)
       | _ -> enum_as_list)
  ;;

  let add_elts_to_enum elts enum =
    Iarray.fold elts ~init:(Enum.to_list_with_trees enum) ~f:(fun acc elt ->
      add_to_enum_as_list acc elt)
    |> Enum.of_list_with_trees
  ;;

  let pair_of_enum_increasing_gen () =
    Generator.union
      [ Generator.both (enum_increasing_gen ()) (enum_increasing_gen ())
      ; (let%map enum0 = enum_increasing_gen ()
         and elts1 = elts_gen
         and elts2 = elts_gen in
         add_elts_to_enum elts1 enum0, add_elts_to_enum elts2 enum0)
      ]
  ;;

  module Int_list = struct
    type t = int list [@@deriving equal, sexp_of]
  end

  module Tree_and_enum_increasing = struct
    type nonrec t =
      (int, (Int.comparator_witness[@sexp.opaque])) Set.Tree.Expert.t
      * ( int
          , (Int.comparator_witness[@sexp.opaque])
          , (Enum.increasing[@sexp.opaque]) )
          Enum.t
    [@@deriving sexp_of]

    let quickcheck_generator = tree_and_enum_increasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Tree_and_enum_decreasing = struct
    type nonrec t =
      (int, (Int.comparator_witness[@sexp.opaque])) Set.Tree.Expert.t
      * ( int
          , (Int.comparator_witness[@sexp.opaque])
          , (Enum.decreasing[@sexp.opaque]) )
          Enum.t
    [@@deriving sexp_of]

    let quickcheck_generator = tree_and_enum_decreasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Tree_increasing = struct
    type t = (int, (Int.comparator_witness[@sexp.opaque])) Set.Tree.Expert.t
    [@@deriving sexp_of]

    let quickcheck_generator = tree_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Tree_and_key = struct
    type nonrec t = (int, (Int.comparator_witness[@sexp.opaque])) Set.Tree.Expert.t * int
    [@@deriving sexp_of]

    let quickcheck_generator =
      Generator.both (tree_gen ()) Generator.small_positive_or_zero_int
    ;;

    let quickcheck_shrinker = Shrinker.atomic
  end

  module Enum_increasing = struct
    type nonrec t =
      ( int
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
        , (Int.comparator_witness[@sexp.opaque])
        , (Enum.decreasing[@sexp.opaque]) )
        Enum.t
    [@@deriving sexp_of]

    let quickcheck_generator = enum_decreasing_gen ()
    let quickcheck_shrinker = Shrinker.atomic
  end

  module Pair_of_enum = struct
    type nonrec t =
      ( int
        , (Int.comparator_witness[@sexp.opaque])
        , (Enum.increasing[@sexp.opaque]) )
        Enum.t
      * ( int
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

type ('a, 'cmp, 'direction) nonempty = ('a, 'cmp, 'direction) Enum.nonempty
and ('a, 'cmp, 'direction) t = ('a, 'cmp, 'direction) Enum.t [@@deriving sexp_of]

let to_list_with_trees = Enum.to_list_with_trees
let of_list_with_trees = Enum.of_list_with_trees

let%expect_test "to_list_with_trees / of_list_with_trees" =
  quickcheck_m (module Enum_increasing) ~f:(fun enum ->
    require_equal
      (module Enum_increasing)
      (Enum.of_list_with_trees (Enum.to_list_with_trees enum))
      enum)
;;

let elt = Enum.elt
let next = Enum.next

let%expect_test "elt & next" =
  quickcheck_m (module Enum_increasing) ~f:(fun enum ->
    require_equal
      (module Int_list)
      (Sequence.unfold ~init:enum ~f:(fun enum ->
         match enum with
         | Null -> None
         | This enum -> Some (Enum.elt enum, Enum.next enum))
       |> Sequence.to_list)
      (List.concat_map (Enum.to_list_with_trees enum) ~f:(fun (x, tree) ->
         x :: Tree.to_list tree)))
;;

let next_decreasing = Enum.next_decreasing

let%expect_test "elt & next_decreasing" =
  quickcheck_m (module Enum_decreasing) ~f:(fun enum ->
    require_equal
      (module Int_list)
      (Sequence.unfold ~init:enum ~f:(fun enum ->
         match enum with
         | Null -> None
         | This enum -> Some (Enum.elt enum, Enum.next_decreasing enum))
       |> Sequence.to_list)
      (List.concat_map (Enum.to_list_with_trees enum) ~f:(fun (x, tree) ->
         x :: List.rev (Tree.to_list tree))))
;;

let cons = Enum.cons

let%expect_test "cons" =
  quickcheck_m (module Tree_and_enum_increasing) ~f:(fun (tree, enum) ->
    require_equal
      (module Int_list)
      (to_list_increasing (Enum.cons tree enum))
      (Set.Tree.to_list tree @ to_list_increasing enum))
;;

let cons_right = Enum.cons_right

let%expect_test "cons_right" =
  quickcheck_m (module Tree_and_enum_decreasing) ~f:(fun (tree, enum) ->
    require_equal
      (module Int_list)
      (to_list_decreasing (Enum.cons_right tree enum))
      (List.rev (Set.Tree.to_list tree) @ to_list_decreasing enum));
  [%expect {| |}]
;;

let of_set = Enum.of_set

let%expect_test "of_set" =
  quickcheck_m (module Tree_increasing) ~f:(fun tree ->
    require_equal
      (module Int_list)
      (to_list_increasing (Enum.of_set tree))
      (Set.Tree.to_list tree))
;;

let of_set_right = Enum.of_set_right

let%expect_test "of_set_right" =
  quickcheck_m (module Tree_increasing) ~f:(fun tree ->
    require_equal
      (module Int_list)
      (to_list_decreasing (Enum.of_set_right tree))
      (List.rev (Set.Tree.to_list tree)));
  [%expect {| |}]
;;

let starting_at_increasing = Enum.starting_at_increasing

let%expect_test "starting_at_increasing" =
  quickcheck_m (module Tree_and_key) ~f:(fun (tree, pos) ->
    require_equal
      (module Int_list)
      (to_list_increasing (Enum.starting_at_increasing tree pos Int.compare))
      (Sequence.to_list
         (Set.Tree.to_sequence
            tree
            ~comparator:Int.comparator
            ~order:`Increasing
            ~greater_or_equal_to:pos)))
;;

let starting_at_decreasing = Enum.starting_at_decreasing

let%expect_test "starting_at_decreasing" =
  quickcheck_m (module Tree_and_key) ~f:(fun (tree, pos) ->
    require_equal
      (module Int_list)
      (to_list_decreasing (Enum.starting_at_decreasing tree pos Int.compare))
      (Sequence.to_list
         (Set.Tree.to_sequence
            tree
            ~comparator:Int.comparator
            ~order:`Decreasing
            ~less_or_equal_to:pos)));
  [%expect {| |}]
;;

let which = Enum.which
let next2 = Enum.next2

let%expect_test "next2" =
  quickcheck_m (module Pair_of_enum) ~f:(fun (enum1, enum2) ->
    require_equal
      (module struct
        type t = (int, int) Map.Merge_element.t list [@@deriving equal, sexp_of]
      end)
      (Sequence.unfold ~init:(enum1, enum2) ~f:(fun (enum1, enum2) ->
         match enum1, enum2 with
         | Null, Null -> None
         | This enum1, Null -> Some (`Left (elt enum1), (next enum1, enum2))
         | Null, This enum2 -> Some (`Right (elt enum2), (enum1, next enum2))
         | This enum1, This enum2 ->
           let which = Enum.which enum1 enum2 ~compare_elt:Int.compare in
           let vs = Enum.which_merge_element enum1 enum2 ~which in
           let enum1, enum2 = Enum.next2 enum1 enum2 ~which in
           Some (vs, (enum1, enum2)))
       |> Sequence.to_list)
      (List.merge
         (to_list_increasing enum1 |> List.map ~f:(fun v -> `Left v))
         (to_list_increasing enum2 |> List.map ~f:(fun v -> `Right v))
         ~compare:(Comparable.lift Int.compare ~f:(fun (`Left x | `Right x) -> x))
       |> List.fold_right ~init:[] ~f:(fun pair acc ->
         match pair, acc with
         | (`Left v1, `Right v2 :: rest | `Right v2, `Left v1 :: rest) when v1 = v2 ->
           `Both (v1, v2) :: rest
         | _ -> (pair :> _ Map.Merge_element.t) :: acc)))
;;

let which_elt = Enum.which_elt
let which_merge_element = Enum.which_merge_element
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
        let whicha = which enum1 enum2 ~compare_elt:Int.compare in
        let whichb =
          which enum1_drop_phys_equal enum2_drop_phys_equal ~compare_elt:Int.compare
        in
        let ak = which_elt enum1 enum2 ~which:whicha in
        let bk = which_elt enum1_drop_phys_equal enum2_drop_phys_equal ~which:whichb in
        let avs = which_merge_element enum1 enum2 ~which:whicha in
        let bvs =
          which_merge_element enum1_drop_phys_equal enum2_drop_phys_equal ~which:whichb
        in
        let a1, a2 = next2 enum1 enum2 ~which:whicha in
        let b1, b2 =
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
                 (ak : int)
                 (bk : int)
                 (avs : (int, int) Map.Merge_element.t)
                 (bvs : (int, int) Map.Merge_element.t)])
      | _ ->
        (match
           (* Fix up when dropping [phys_equal] parts caused the outer match to fail *)
           match enum1, enum2 with
           | Null, _ | _, Null -> None
           | This enum1, This enum2 ->
             (match which enum1 enum2 ~compare_elt:Int.compare with
              | Both as which when phys_equal (Enum.elt enum1) (Enum.elt enum2) ->
                let enum1, enum2 = Enum.next2 enum1 enum2 ~which in
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
                 (enum1 : (int, _, _) t)
                 (enum2 : (int, _, _) t)
                 (enum1_drop_phys_equal : (int, _, _) t)
                 (enum2_drop_phys_equal : (int, _, _) t)])
    in
    loop (enum1, enum2) (enum1, enum2));
  [%expect {| |}]
;;
