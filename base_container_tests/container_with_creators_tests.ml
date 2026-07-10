open! Base
open Base_container_tests_intf.Definitions
open Base_quickcheck.Export
open Expect_test_helpers_base

(* Provides test coverage for [Container.Generic_with_creators]. *)
module%template
  [@alloc a_run @ l_run = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Container_generic_with_creators
  [@alloc a_run])
    (Container_already_tested : Container.Generic
                                [@alloc a_run]
                                with type 'a elt := 'a Impl.Elt.t
                                 and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) Impl.t) =
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

  (* As in [container_tests.ml], we define all tests in a single [let ... and]. *)

  let%template () = ()

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] of_list =
    let of_list_ = Impl.of_list [@alloc a] in
    (test_fn [@mode.explicit l])
      of_list_
      (module struct
        type t = Elt.t list [@@deriving quickcheck ~generator ~shrinker, sexp_of]
      end)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"round-trip via of_list/to_list"
      ~actual:(fun of_list list ->
        (of_list list |> (Impl.to_list [@alloc a]) |> (Sort.actual [@mode l]))
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun list -> Sort.expect list)
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    of_list_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] of_array =
    let of_array_ = Impl.of_array [@alloc a] in
    (test_fn [@mode.explicit l])
      of_array_
      (module struct
        type t = Elt.t array [@@deriving quickcheck ~generator ~shrinker, sexp_of]
      end)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"round-trip via of_array/to_array"
      ~actual:(fun of_array array ->
        (of_array array |> (Impl.to_list [@alloc a]) |> (Sort.actual [@mode l]))
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun array -> Sort.expect (Array.to_list array))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    of_array_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] append =
    let append_ = Impl.append [@alloc a] in
    (test_fn [@mode.explicit l])
      append_
      (module struct
        type t = Cont.t * Cont.t [@@deriving quickcheck ~generator ~shrinker, sexp_of]
      end)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"append two containers"
      ~actual:(fun append (fst, snd) -> append fst snd [@exclave_if_stack a])
      ~expect:(fun (fst, snd) -> Impl.of_list (Impl.to_list fst @ Impl.to_list snd))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    append_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] concat =
    let concat_ = Impl.concat [@alloc a] in
    (test_fn [@mode.explicit l])
      concat_
      (module Concat)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"concatenation"
      ~actual:(fun concat cc -> concat cc [@exclave_if_stack a])
      ~expect:(fun cc ->
        Impl.of_list (List.concat_map ~f:Impl.to_list (Concat.to_list cc)))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    concat_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] map =
    let map_ = Impl.map [@mode li] [@alloc a] in
    (test_fn [@mode.explicit lo])
      map_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"raise every element to at least the sample"
      ~actual:(fun map { container; sample } ->
        map container ~f:(fun x ->
          ((Comparable.max [@mode li]) (Elt.compare [@mode li]) sample x
           |> (elt_smart_globalize [@mode li lo]))
          [@nontail] [@exclave_if_stack a])
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        List.map (Impl.to_list container) ~f:(fun elt ->
          Comparable.max Elt.compare sample elt)
        |> Impl.of_list)
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    map_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] filter =
    let filter_ = Impl.filter [@alloc a] in
    (test_fn [@mode.explicit l])
      filter_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"every element less than or equal to the sample"
      ~actual:(fun filter { container; sample } ->
        filter container ~f:(fun x -> (Elt.compare [@mode l]) x sample <= 0)
        [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        Impl.fold container ~init:[] ~f:(fun list x ->
          if Elt.compare x sample <= 0 then x :: list else list)
        |> List.rev
        |> Impl.of_list)
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    filter_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] filter_map
    =
    let filter_map_ = Impl.filter_map [@mode li] [@alloc a] in
    (test_fn [@mode.explicit lo])
      filter_map_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"every element not equal to the sample, raised to at least the sample"
      ~actual:(fun filter_map { container; sample } ->
        filter_map container ~f:(fun x ->
          match[@exclave_if_stack a]
            Ordering.of_int ((Elt.compare [@mode li]) x sample)
          with
          | Less -> Some sample
          | Equal -> None
          | Greater -> Some ((elt_smart_globalize [@mode li lo]) x))
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        Impl.filter container ~f:(Fn.non (Elt.equal sample))
        |> Impl.map ~f:(fun x -> Comparable.max Elt.compare sample x))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    filter_map_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] concat_map
    =
    let concat_map_ = Impl.concat_map [@mode li] [@alloc a] in
    (test_fn [@mode.explicit lo])
      concat_map_
      (module Cont_with_sample)
      (module Cont)
      ~name:[%loc.this_function_name]
      ~description:"follow every element by the sample"
      ~actual:(fun concat_map { container; sample } ->
        concat_map container ~f:(fun x ->
          (Impl.of_list [@alloc a])
            [ (elt_smart_globalize [@mode li lo]) x; sample ]
          [@nontail] [@exclave_if_stack a])
        [@nontail] [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        List.concat_map (Impl.to_list container) ~f:(fun x -> [ x; sample ])
        |> Impl.of_list)
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    concat_map_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] partition_tf =
    let partition_tf_ = Impl.partition_tf [@alloc a] in
    (test_fn [@mode.explicit l])
      partition_tf_
      (module Cont_with_sample)
      (module struct
        type t = Cont.t * Cont.t [@@deriving (equal [@mode l]), (sexp_of [@alloc a])]
      end)
      ~name:[%loc.this_function_name]
      ~description:
        "split elements less than or equal to the sample from elements greater than the \
         sample"
      ~actual:(fun partition_tf { container; sample } ->
        partition_tf container ~f:(fun x -> (Elt.compare [@mode l]) x sample <= 0)
        [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        ( Impl.filter container ~f:(fun x -> Elt.compare x sample <= 0)
        , Impl.filter container ~f:(fun x -> Elt.compare x sample > 0) ))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    partition_tf_

  and[@mode li = (global, l_run)] [@alloc a @ lo = (heap @ global, a_run @ l_run)] partition_map
    =
    let partition_map_ = Impl.partition_map [@mode li] [@alloc a] in
    (test_fn [@mode.explicit lo])
      partition_map_
      (module Cont_with_sample)
      (module struct
        type t = Cont.t * Cont.t [@@deriving (equal [@mode lo]), (sexp_of [@alloc a])]
      end)
      ~name:[%loc.this_function_name]
      ~description:
        "on left, elements less than or equal to the sample; on right, elements greater \
         than the sample replaced by the sample"
      ~actual:(fun partition_map { container; sample } ->
        partition_map container ~f:(fun x ->
          if [@exclave_if_stack a] (Elt.compare [@mode li]) x sample <= 0
          then First ((elt_smart_globalize [@mode li lo]) x)
          else Second sample)
        [@exclave_if_stack a])
      ~expect:(fun { container; sample } ->
        ( Impl.filter container ~f:(fun x -> Elt.compare x sample <= 0)
        , Impl.filter container ~f:(fun x -> Elt.compare x sample > 0)
          |> Impl.map ~f:(fun _ -> sample) ))
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    partition_map_
  ;;

  (* We [include] previously tested bindings at the end. Previous tests still need to
     refer to [Impl] explicitly for these functions. *)
  include Container_already_tested
end

[%%template
[@@@alloc.default a @ l = (heap_global, stack_local)]

(* Wraps and exports [Run] as a function. *)
let test_container_generic_with_creators
  ?(cr = CR.CR)
  ?(duplicates = Duplicates.Keep)
  ?(order = Order.Original)
  ?(quickcheck_config = Base_quickcheck.Test.default_config)
  ?(check_no_allocation = false)
  (module Impl : Container_generic_with_creators[@alloc a])
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
      module type S = Container.Generic_with_creators [@alloc a]

      module Run () = struct
        open struct
          module Container = Container_tests.Run [@alloc a] (Config) (Impl)
        end

        include Run [@alloc a] (Config) (Impl) (Container)
      end
    end)
;;

(* Instantiates [test_container_generic_with_creators] for [Container.S0]. *)
let test_container_s0_with_creators
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Container_s0_with_creators[@alloc a])
  =
  (test_container_generic_with_creators [@alloc a])
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

        type 'a t = Impl.t
        [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

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

(* Instantiates [test_container_generic_with_creators] for [Container.S1_with_creators].
*)
let test_container_s1_with_creators
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Container_s1_with_creators[@alloc a])
  =
  (test_container_generic_with_creators [@alloc a])
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
