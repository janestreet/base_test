open! Base
open Base_container_tests_intf.Definitions
open Base_quickcheck.Export
open Expect_test_helpers_base

(* Provides test coverage for [Indexed_container.Generic_with_creators]. *)
module Run
    (Config : Helpers.Config)
    (Impl : Indexed_container_generic_with_creators)
    (Container_with_creators_already_tested : Container.Generic_with_creators
                                              with type 'a elt := 'a Impl.Elt.t
                                               and type ('a, 'p1, 'p2) t :=
                                                ('a, 'p1, 'p2) Impl.t
                                               and type ('a, 'p1, 'p2) concat :=
                                                ('a, 'p1, 'p2) Impl.concat)
    (Indexed_container_already_tested : Indexed_container.Generic
                                        with type 'a elt := 'a Impl.Elt.t
                                         and type ('a, 'p1, 'p2) t :=
                                          ('a, 'p1, 'p2) Impl.t) =
struct
  type 'a elt = 'a Impl.Elt.t
  type ('a, 'phantom1, 'phantom2) t = ('a, 'phantom1, 'phantom2) Impl.t
  type ('a, 'phantom1, 'phantom2) concat = ('a, 'phantom1, 'phantom2) Impl.concat

  (* We instantiate helpers for testing [Impl]. *)
  open
    Helpers.Test
      (Config)
      (struct
        module Elt = Impl.Elt
        module Cont = Impl.Simple
        module Concat = Impl.Simple.Concat
      end)

  open Locality

  let sort_expect_list_of_cont cont =
    cont |> Impl.to_list |> elt_list_globalize |> Sort.expect
  ;;

  (* As in [container_tests.ml], we define all tests in a single [let ... and]. *)

  let () = ()

  and init =
    let init_ = Impl.init in
    test_fn
      init_
      (module struct
        type t = Elt.t array [@@deriving quickcheck ~generator ~shrinker, sexp_of]
      end)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"round-trip via to_array/init"
      ~actual:(fun init array ->
        init (Array.length array) ~f:(fun i -> Array.get array i) [@nontail])
      ~expect:(fun array -> Impl.of_array array)
      ~expect_no_allocation:(is_stack alloc);
    init_

  and mapi =
    let mapi_ = Impl.mapi in
    test_fn_nondeterministic
      mapi_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"replace first element with sample"
      ~actual:(fun mapi { container; sample } ->
        mapi container ~f:(fun i x -> if i = 0 then sample else elt_smart_globalize x)
        [@nontail])
      ~expect:(fun { container; sample } ->
        match Impl.to_list container with
        | [] -> container
        | _ :: list -> Impl.of_list (sample :: list))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let input = Sort.expect (Impl.to_list container) in
        let output = sort_expect_list_of_cont output in
        if [%equal: Elt.t list] input output
        then List.is_empty input || List.mem input sample ~equal:Elt.equal
        else
          List.existsi input ~f:(fun i x ->
            (not (Elt.equal x sample))
            && [%equal: Elt.t list]
                 output
                 (Sort.expect
                    (List.mapi input ~f:(fun j y -> if i = j then sample else y)))))
      ~expect_no_allocation:(is_stack alloc);
    mapi_

  and filteri =
    let filteri_ = Impl.filteri in
    test_fn_nondeterministic
      filteri_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"all elements <= sample after first element"
      ~actual:(fun filteri { container; sample } ->
        filteri container ~f:(fun i x -> i > 0 && Elt.compare x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.of_list (List.drop (Impl.to_list container) 1)
        |> Impl.filter ~f:(fun x -> Elt.compare x sample <= 0))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let input =
          List.filter (Impl.to_list container) ~f:(fun x -> Elt.compare x sample <= 0)
          |> Sort.expect
        in
        let output = sort_expect_list_of_cont output in
        [%equal: Elt.t list] input output
        || List.existsi input ~f:(fun i _ ->
          [%equal: Elt.t list] output (List.filteri input ~f:(fun j _ -> i <> j))))
      ~expect_no_allocation:(is_stack alloc);
    filteri_

  and filter_mapi =
    let filter_mapi_ = Impl.filter_mapi in
    test_fn_nondeterministic
      filter_mapi_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"all elements after first element, raised to at least sample"
      ~actual:(fun filter_mapi { container; sample } ->
        filter_mapi container ~f:(fun i x ->
          if i = 0
          then None
          else if Elt.compare x sample <= 0
          then Some sample
          else Some (elt_smart_globalize x))
        [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.of_list (List.drop (Impl.to_list container) 1)
        |> Impl.map ~f:(fun x -> Comparable.max Elt.compare sample x))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let input =
          List.map (Impl.to_list container) ~f:(fun x ->
            if Elt.compare x sample <= 0 then sample else x)
          |> Sort.expect
        in
        let output = sort_expect_list_of_cont output in
        [%equal: Elt.t list] input output
        || List.existsi input ~f:(fun i _ ->
          [%equal: Elt.t list] output (List.filteri input ~f:(fun j _ -> i <> j))))
      ~expect_no_allocation:(is_stack alloc);
    filter_mapi_

  and concat_mapi =
    let concat_mapi_ = Impl.concat_mapi in
    test_fn_nondeterministic
      concat_mapi_
      (module Cont)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"two of each element except the first"
      ~actual:(fun concat_mapi container ->
        concat_mapi container ~f:(fun i elt ->
          if i = 0
          then Impl.of_list []
          else Impl.of_list [ elt_smart_globalize elt; elt_smart_globalize elt ])
        [@nontail])
      ~expect:(fun container ->
        List.concat_mapi (Impl.to_list container) ~f:(fun i elt ->
          if i = 0 then [] else [ elt; elt ])
        |> Impl.of_list)
      ~expect_if_unpredictable:(fun input output ->
        if Impl.is_empty input
        then Impl.is_empty output
        else (
          let input = Sort.expect (Impl.to_list input) in
          let output = sort_expect_list_of_cont output in
          List.existsi input ~f:(fun i _ ->
            [%equal: Elt.t list]
              output
              (Sort.expect
                 (List.concat_mapi input ~f:(fun j elt ->
                    if i = j then [] else [ elt; elt ]))))))
      ~expect_no_allocation:(is_stack alloc);
    concat_mapi_

  and partitioni_tf =
    let partitioni_tf_ = Impl.partitioni_tf in
    test_fn_nondeterministic
      partitioni_tf_
      (module Cont_with_sample)
      (module struct
        type t = Cont.t * Cont.t [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"partition elements <= sample after first element"
      ~actual:(fun partitioni_tf { container; sample } ->
        partitioni_tf container ~f:(fun i x -> i > 0 && Elt.compare x sample <= 0)
        [@nontail])
      ~expect:(fun { container; sample } ->
        ( Impl.filteri container ~f:(fun i x -> i > 0 && Elt.compare x sample <= 0)
        , Impl.filteri container ~f:(fun i x -> i = 0 || Elt.compare x sample > 0) ))
      ~expect_if_unpredictable:(fun { container; sample } (a, b) ->
        let input = Sort.expect (Impl.to_list container) in
        let a = sort_expect_list_of_cont a in
        let b = sort_expect_list_of_cont b in
        let less, more =
          List.partition_tf input ~f:(fun x -> Elt.compare x sample <= 0)
        in
        [%equal: Elt.t list * Elt.t list] (a, b) (less, more)
        || List.existsi less ~f:(fun i one ->
          let others = List.filteri less ~f:(fun j _ -> i <> j) in
          [%equal: Elt.t list * Elt.t list]
            (a, b)
            (Sort.expect others, Sort.expect (one :: more))))
      ~expect_no_allocation:(is_stack alloc);
    partitioni_tf_

  and partition_mapi =
    let partition_mapi_ = Impl.partition_mapi in
    test_fn_nondeterministic
      partition_mapi_
      (module Cont_with_sample)
      (module struct
        type t = Cont.t * Cont.t [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"partition <= sample after first element"
      ~actual:(fun partition_mapi { container; sample } ->
        partition_mapi container ~f:(fun i x ->
          if i > 0 && Elt.compare x sample <= 0
          then First (elt_smart_globalize x)
          else Second (elt_smart_globalize x))
        [@nontail])
      ~expect:(fun { container; sample } ->
        ( Impl.filteri container ~f:(fun i x -> i > 0 && Elt.compare x sample <= 0)
        , Impl.filteri container ~f:(fun i x -> i = 0 || Elt.compare x sample > 0) ))
      ~expect_if_unpredictable:(fun { container; sample } (a, b) ->
        let input = Sort.expect (Impl.to_list container) in
        let a = sort_expect_list_of_cont a in
        let b = sort_expect_list_of_cont b in
        let less, more =
          List.partition_tf input ~f:(fun x -> Elt.compare x sample <= 0)
        in
        [%equal: Elt.t list * Elt.t list] (a, b) (less, more)
        || List.existsi less ~f:(fun i one ->
          let others = List.filteri less ~f:(fun j _ -> i <> j) in
          [%equal: Elt.t list * Elt.t list]
            (a, b)
            (Sort.expect others, Sort.expect (one :: more))))
      ~expect_no_allocation:(is_stack alloc);
    partition_mapi_
  ;;

  (* We [include] previously tested bindings at the end. Previous tests still need to
     refer to [Impl] explicitly for these functions. *)
  include Container_with_creators_already_tested
  include Indexed_container_already_tested
end

(* Wraps and exports [Run] as a function. *)
let test_indexed_container_generic_with_creators
  ?(cr = CR.CR)
  ?(duplicates = Duplicates.Keep)
  ?(order = Order.Original)
  ?(quickcheck_config = Base_quickcheck.Test.default_config)
  ?(check_no_allocation = false)
  (module Impl : Indexed_container_generic_with_creators)
  =
  let module Config = struct
    let cr = cr
    let duplicates = duplicates
    let order = order
    let quickcheck_config = quickcheck_config
    let check_no_allocation = check_no_allocation
  end
  in
  Helpers.test_m
    (module struct
      module type S = Indexed_container.Generic_with_creators

      module Run () = struct
        open struct
          module Container = Container_tests.Run (Config) (Impl)

          module Container_with_creators =
            Container_with_creators_tests.Run (Config) (Impl) (Container)

          module Indexed = Indexed_container_tests.Run (Config) (Impl) (Container)
        end

        include Run (Config) (Impl) (Container_with_creators) (Indexed)
      end
    end)
;;

(* Instantiates [test_indexed_container_generic_with_creators] for [Indexed_container.S0].
*)
let test_indexed_container_s0_with_creators
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Indexed_container_s0_with_creators)
  =
  test_indexed_container_generic_with_creators
    ?cr
    ?duplicates
    ?order
    ?quickcheck_config
    ?check_no_allocation
    (module struct
      include Impl

      module Elt = struct
        type _ t = Impl.Elt.t [@@deriving compare, equal, quickcheck, sexp_of, globalize]
      end

      module Simple = struct
        type phantom1 = Nothing.t
        type phantom2 = Nothing.t
        type _ t = Impl.t [@@deriving equal, quickcheck, sexp_of]

        module Concat = struct
          type 'a t = 'a list [@@deriving equal, quickcheck, sexp_of]

          let to_list = Fn.id
          let of_list = Fn.id
        end
      end

      type (_, _, _) t = Impl.t
      type ('a, _, _) concat = 'a list

      let mem t x ~equal:_ = Impl.mem t x
    end)
;;

(* Instantiates [test_indexed_container_generic_with_creators] for
   [Indexed_container.S1_with_creators]. *)
let test_indexed_container_s1_with_creators
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Indexed_container_s1_with_creators)
  =
  test_indexed_container_generic_with_creators
    ?cr
    ?duplicates
    ?order
    ?quickcheck_config
    ?check_no_allocation
    (module struct
      include Impl

      module Elt = struct
        type 'a t = 'a [@@deriving compare, equal, quickcheck, sexp_of, globalize]
      end

      module Simple = struct
        type phantom1 = Nothing.t
        type phantom2 = Nothing.t
        type 'a t = 'a Impl.t [@@deriving equal, quickcheck, sexp_of]

        module Concat = Impl
      end

      type ('a, _, _) t = 'a Impl.t
      type ('a, _, _) concat = 'a Impl.t
    end)
;;
