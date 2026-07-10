open! Base
open Base_container_tests_intf.Definitions
open Base_quickcheck.Export
open Expect_test_helpers_base

(* Provides test coverage for [Indexed_container.Generic_with_creators]. *)
module%template
  [@alloc a_run @ l_run = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Indexed_container_generic_with_creators
  [@alloc a_run])
    (Container_with_creators_already_tested : Container.Generic_with_creators
                                              [@alloc a_run]
                                              with type 'a elt := 'a Impl.Elt.t
                                               and type ('a, 'p1, 'p2) t :=
                                                ('a, 'p1, 'p2) Impl.t
                                               and type ('a, 'p1, 'p2) concat :=
                                                ('a, 'p1, 'p2) Impl.concat)
    (Indexed_container_already_tested : Indexed_container.Generic
                                        [@alloc a_run]
                                        with type 'a elt := 'a Impl.Elt.t
                                         and type ('a, 'p1, 'p2) t :=
                                          ('a, 'p1, 'p2) Impl.t) =
struct
  type 'a elt = 'a Impl.Elt.t
  type ('a, 'phantom1, 'phantom2) t = ('a, 'phantom1, 'phantom2) Impl.t
  type ('a, 'phantom1, 'phantom2) concat = ('a, 'phantom1, 'phantom2) Impl.concat

  (* We instantiate helpers for testing [Impl]. *)
  open
    Helpers.Test [@alloc a_run]
      (Config)
      (struct
        module Elt = Impl.Elt
        module Cont = Impl.Simple
        module Concat = Impl.Simple.Concat
      end)

  open Locality

  let[@alloc a = (heap, a_run)] sort_expect_list_of_cont cont =
    cont |> (Impl.to_list [@alloc a]) |> elt_list_globalize |> Sort.expect
  ;;

  (* As in [container_tests.ml], we define all tests in a single [let ... and]. *)

  let%template () = ()

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] init =
    let init_ = Impl.init [@alloc a] in
    (test_fn [@mode.explicit l])
      init_
      (module struct
        type t = Elt.t array [@@deriving quickcheck ~generator ~shrinker, sexp_of]
      end)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"round-trip via to_array/init"
      ~actual:(fun init array ->
        init (Array.length array) ~f:(fun i -> Array.get array i)
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun array -> Impl.of_array array)
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    init_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] mapi =
    let mapi_ = Impl.mapi [@mode li] [@alloc a] in
    (test_fn_nondeterministic [@mode.explicit lo])
      mapi_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"replace first element with sample"
      ~actual:(fun mapi { container; sample } ->
        mapi container ~f:(fun i x ->
          if i = 0
          then sample
          else (elt_smart_globalize [@mode li lo]) x [@exclave_if_stack a])
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        match Impl.to_list container with
        | [] -> container
        | _ :: list -> Impl.of_list (sample :: list))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let input = Sort.expect (Impl.to_list container) in
        let output = (sort_expect_list_of_cont [@alloc a]) output in
        if [%equal: Elt.t list] input output
        then List.is_empty input || List.mem input sample ~equal:Elt.equal
        else
          List.existsi input ~f:(fun i x ->
            (not (Elt.equal x sample))
            && [%equal: Elt.t list]
                 output
                 (Sort.expect
                    (List.mapi input ~f:(fun j y -> if i = j then sample else y)))))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    mapi_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] filteri =
    let filteri_ = Impl.filteri [@alloc a] in
    (test_fn_nondeterministic [@mode.explicit l])
      filteri_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"all elements <= sample after first element"
      ~actual:(fun filteri { container; sample } ->
        filteri container ~f:(fun i x -> i > 0 && (Elt.compare [@mode l]) x sample <= 0)
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        Impl.of_list (List.drop (Impl.to_list container) 1)
        |> Impl.filter ~f:(fun x -> Elt.compare x sample <= 0))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let input =
          List.filter (Impl.to_list container) ~f:(fun x -> Elt.compare x sample <= 0)
          |> Sort.expect
        in
        let output = (sort_expect_list_of_cont [@alloc a]) output in
        [%equal: Elt.t list] input output
        || List.existsi input ~f:(fun i _ ->
          [%equal: Elt.t list] output (List.filteri input ~f:(fun j _ -> i <> j))))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    filteri_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] filter_mapi
    =
    let filter_mapi_ = Impl.filter_mapi [@mode li] [@alloc a] in
    (test_fn_nondeterministic [@mode.explicit lo])
      filter_mapi_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"all elements after first element, raised to at least sample"
      ~actual:(fun filter_mapi { container; sample } ->
        filter_mapi container ~f:(fun i x ->
          if [@exclave_if_stack a] i = 0
          then None
          else if (Elt.compare [@mode li]) x sample <= 0
          then Some sample
          else Some ((elt_smart_globalize [@mode li lo]) x))
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        Impl.of_list (List.drop (Impl.to_list container) 1)
        |> Impl.map ~f:(fun x -> Comparable.max Elt.compare sample x))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let input =
          List.map (Impl.to_list container) ~f:(fun x ->
            if Elt.compare x sample <= 0 then sample else x)
          |> Sort.expect
        in
        let output = (sort_expect_list_of_cont [@alloc a]) output in
        [%equal: Elt.t list] input output
        || List.existsi input ~f:(fun i _ ->
          [%equal: Elt.t list] output (List.filteri input ~f:(fun j _ -> i <> j))))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    filter_mapi_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] concat_mapi
    =
    let concat_mapi_ = Impl.concat_mapi [@mode li] [@alloc a] in
    (test_fn_nondeterministic [@mode.explicit lo])
      concat_mapi_
      (module Cont)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"two of each element except the first"
      ~actual:(fun concat_mapi container ->
        concat_mapi container ~f:(fun i elt ->
          if [@exclave_if_stack a] i = 0
          then (Impl.of_list [@alloc a]) []
          else
            (Impl.of_list [@alloc a])
              [ (elt_smart_globalize [@mode li lo]) elt
              ; (elt_smart_globalize [@mode li lo]) elt
              ])
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun container ->
        List.concat_mapi (Impl.to_list container) ~f:(fun i elt ->
          if i = 0 then [] else [ elt; elt ])
        |> Impl.of_list)
      ~expect_if_unpredictable:(fun input output ->
        if Impl.is_empty input
        then Impl.is_empty output
        else (
          let input = Sort.expect (Impl.to_list input) in
          let output = (sort_expect_list_of_cont [@alloc a]) output in
          List.existsi input ~f:(fun i _ ->
            [%equal: Elt.t list]
              output
              (Sort.expect
                 (List.concat_mapi input ~f:(fun j elt ->
                    if i = j then [] else [ elt; elt ]))))))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    concat_mapi_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] partitioni_tf =
    let partitioni_tf_ = Impl.partitioni_tf [@alloc a] in
    (test_fn_nondeterministic [@mode.explicit l])
      partitioni_tf_
      (module Cont_with_sample)
      (module struct
        type t = Cont.t * Cont.t [@@deriving (equal [@mode l]), (sexp_of [@alloc a])]
      end)
      ~name:[%loc.this_function_name]
      ~description:"partition elements <= sample after first element"
      ~actual:(fun partitioni_tf { container; sample } ->
        partitioni_tf container ~f:(fun i x ->
          i > 0 && (Elt.compare [@mode l]) x sample <= 0)
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        ( Impl.filteri container ~f:(fun i x -> i > 0 && Elt.compare x sample <= 0)
        , Impl.filteri container ~f:(fun i x -> i = 0 || Elt.compare x sample > 0) ))
      ~expect_if_unpredictable:(fun { container; sample } (a, b) ->
        let input = Sort.expect (Impl.to_list container) in
        let a = (sort_expect_list_of_cont [@alloc a]) a in
        let b = (sort_expect_list_of_cont [@alloc a]) b in
        let less, more =
          List.partition_tf input ~f:(fun x -> Elt.compare x sample <= 0)
        in
        [%equal: Elt.t list * Elt.t list] (a, b) (less, more)
        || List.existsi less ~f:(fun i one ->
          let others = List.filteri less ~f:(fun j _ -> i <> j) in
          [%equal: Elt.t list * Elt.t list]
            (a, b)
            (Sort.expect others, Sort.expect (one :: more))))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    partitioni_tf_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] partition_mapi
    =
    let partition_mapi_ = Impl.partition_mapi [@mode li] [@alloc a] in
    (test_fn_nondeterministic [@mode.explicit lo])
      partition_mapi_
      (module Cont_with_sample)
      (module struct
        type t = Cont.t * Cont.t [@@deriving (equal [@mode lo]), (sexp_of [@alloc a])]
      end)
      ~name:[%loc.this_function_name]
      ~description:"partition <= sample after first element"
      ~actual:(fun partition_mapi { container; sample } ->
        partition_mapi container ~f:(fun i x ->
          if [@exclave_if_stack a] i > 0 && (Elt.compare [@mode li]) x sample <= 0
          then First ((elt_smart_globalize [@mode li lo]) x)
          else Second ((elt_smart_globalize [@mode li lo]) x))
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        ( Impl.filteri container ~f:(fun i x -> i > 0 && Elt.compare x sample <= 0)
        , Impl.filteri container ~f:(fun i x -> i = 0 || Elt.compare x sample > 0) ))
      ~expect_if_unpredictable:(fun { container; sample } (a, b) ->
        let input = Sort.expect (Impl.to_list container) in
        let a = (sort_expect_list_of_cont [@alloc a]) a in
        let b = (sort_expect_list_of_cont [@alloc a]) b in
        let less, more =
          List.partition_tf input ~f:(fun x -> Elt.compare x sample <= 0)
        in
        [%equal: Elt.t list * Elt.t list] (a, b) (less, more)
        || List.existsi less ~f:(fun i one ->
          let others = List.filteri less ~f:(fun j _ -> i <> j) in
          [%equal: Elt.t list * Elt.t list]
            (a, b)
            (Sort.expect others, Sort.expect (one :: more))))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    partition_mapi_
  ;;

  (* We [include] previously tested bindings at the end. Previous tests still need to
     refer to [Impl] explicitly for these functions. *)
  include Container_with_creators_already_tested
  include Indexed_container_already_tested
end

[%%template
[@@@alloc.default a @ l = (heap_global, stack_local)]

(* Wraps and exports [Run] as a function. *)
let test_indexed_container_generic_with_creators
  ?(cr = CR.CR)
  ?(duplicates = Duplicates.Keep)
  ?(order = Order.Original)
  ?(quickcheck_config = Base_quickcheck.Test.default_config)
  ?(check_no_allocation = false)
  (module Impl : Indexed_container_generic_with_creators[@alloc a])
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
      module type S = Indexed_container.Generic_with_creators [@alloc a]

      module Run () = struct
        open struct
          module Container = Container_tests.Run [@alloc a] (Config) (Impl)

          module Container_with_creators =
            Container_with_creators_tests.Run [@alloc a] (Config) (Impl) (Container)

          module Indexed =
            Indexed_container_tests.Run [@alloc a] (Config) (Impl) (Container)
        end

        include Run [@alloc a] (Config) (Impl) (Container_with_creators) (Indexed)
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
  (module Impl : Indexed_container_s0_with_creators[@alloc a])
  =
  (test_indexed_container_generic_with_creators [@alloc a])
    ?cr
    ?duplicates
    ?order
    ?quickcheck_config
    ?check_no_allocation
    (module struct
      include Impl

      module Elt = struct
        type _ t = Impl.Elt.t
        [@@deriving
          compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
      end

      module Simple = struct
        type phantom1 = Nothing.t
        type phantom2 = Nothing.t
        type _ t = Impl.t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

        module Concat = struct
          type 'a t = 'a list [@@deriving equal, quickcheck, sexp_of]

          let to_list = Fn.id
          let of_list = Fn.id
        end
      end

      type (_, _, _) t = Impl.t
      type ('a, _, _) concat = 'a list

      let%template[@mode l = (global, l)] mem t x ~equal:_ = (Impl.mem [@mode l]) t x
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
  (module Impl : Indexed_container_s1_with_creators[@alloc a])
  =
  (test_indexed_container_generic_with_creators [@alloc a])
    ?cr
    ?duplicates
    ?order
    ?quickcheck_config
    ?check_no_allocation
    (module struct
      include Impl

      module Elt = struct
        type 'a t = 'a
        [@@deriving
          compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
      end

      module Simple = struct
        type phantom1 = Nothing.t
        type phantom2 = Nothing.t

        type 'a t = 'a Impl.t
        [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

        module Concat = Impl
      end

      type ('a, _, _) t = 'a Impl.t
      type ('a, _, _) concat = 'a Impl.t
    end)
;;]
