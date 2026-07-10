open! Base
open Base_container_tests_intf.Definitions
open Expect_test_helpers_base

(* Provides test coverage for [Container.Generic]. *)
module%template
  [@alloc a_run @ l_run = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Container_generic
  [@alloc a_run]) =
struct
  type 'a elt = 'a Impl.Elt.t
  type ('a, 'phantom1, 'phantom2) t = ('a, 'phantom1, 'phantom2) Impl.t

  (* We instantiate helpers for testing [Impl]. *)
  open
    Helpers.Test [@alloc a_run]
      (Config)
      (struct
        module Elt = Impl.Elt
        module Cont = Impl.Simple
        module Concat = List
      end)

  open Locality

  (* We define every function in a single [let ... and]. This forces all references to
     explicitly specify [Impl], as the function names are not in scope inside the body
     expressions.

     In each definition, we first test the function, then we return the function. It would
     be more convenient if the various tests could just pass the function through, but
     that does not preserve polymorphic types.

     In templated tests, for a templated container function [fn] we introduce a binding
     [fn_] with [fn] fully instantiated, and modify [name] to include string
     representations of the template parameters. Currently, we omit template parameters in
     test names at [Run] with [@alloc heap].
  *)

  let () = ()

  and length =
    let length_ = Impl.length in
    (test_fn [@mode.explicit global])
      length_
      (module Cont)
      (module Int)
      ~name:[%loc.this_function_name]
      ~description:"container length"
      ~actual:(fun length t -> length t)
      ~expect:(fun t -> Impl.fold t ~init:0 ~f:(fun n _ -> n + 1))
      ~expect_no_allocation:true;
    length_

  and is_empty =
    let is_empty_ = Impl.is_empty in
    (test_fn [@mode.explicit global])
      is_empty_
      (module Cont)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"is the container empty"
      ~actual:(fun is_empty t -> is_empty t)
      ~expect:(fun t -> Impl.length t = 0)
      ~expect_no_allocation:true;
    is_empty_

  and[@mode l = (global, l_run)] mem =
    let mem_ = Impl.mem [@mode l] in
    (test_fn [@mode.explicit global])
      mem_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"does the container include the sample"
      ~actual:(fun mem { container; sample } ->
        mem container sample ~equal:(Elt.equal [@mode l]))
      ~expect:(fun { container; sample } ->
        Impl.exists container ~f:((Elt.equal [@mode l]) sample) [@nontail])
      ~expect_no_allocation:true;
    mem_

  and[@mode l = (global, l_run)] iter =
    let iter_ = Impl.iter [@mode l] in
    (test_fn [@mode.explicit global])
      iter_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"elements of the container"
      ~actual:(fun iter container ->
        let q = Queue.create () in
        iter container ~f:(fun elt ->
          Queue.enqueue q ((elt_smart_globalize [@mode l global]) elt));
        Sort.actual (Queue.to_list q))
      ~expect:(fun container -> Sort.expect (Impl.to_list container))
      ~expect_no_allocation:false
    (* This test cannot check for allocation because we allocate the queue *);
    if Config.check_no_allocation
    then
      (test_fn [@mode.explicit global])
        iter_
        (module Cont_with_sample)
        (module Int)
        ~name:[%loc.this_function_name]
        ~description:"balance of comparisons against sample"
        ~actual:(fun iter { container; sample } ->
          let r = ref 0 in
          iter container ~f:(fun x -> r := !r + (Elt.compare [@mode l]) x sample)
          [@nontail];
          !r)
        ~expect:(fun { container; sample } ->
          Impl.fold container ~init:0 ~f:(fun n x -> n + (Elt.compare [@mode l]) x sample))
        ~expect_no_allocation:true;
    iter_

  and[@mode li = (global, l_run), lo = (global, l_run)] iter_until =
    let iter_until_ = Impl.iter_until [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      iter_until_
      (module Cont_with_sample)
      (module struct
        type t = (unit, string) Result.t [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or Ok if all > sample"
      ~actual:(fun iter_until { container; sample } ->
        iter_until
          container
          ~f:(fun x ->
            match[@exclave_if_local lo ~reasons:[ Will_return_unboxed ]]
              Ordering.of_int ((Elt.compare [@mode local]) x sample)
            with
            | Less -> Stop (Error "too small")
            | Equal -> Stop (Error "borderline")
            | Greater -> Continue ())
          ~finish:(result_return [@mode lo])
        [@nontail] [@exclave_if_local lo ~reasons:[ Will_return_unboxed ]])
      ~expect:(fun { container; sample } ->
        List.iter_until
          (Impl.to_list container)
          ~f:(fun x ->
            match Ordering.of_int (Elt.compare x sample) with
            | Less -> Stop (Error "too small")
            | Equal -> Stop (Error "borderline")
            | Greater -> Continue ())
          ~finish:Result.return)
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | Ok () -> not (List.exists list ~f:(fun x -> Elt.compare x sample <= 0))
        | Error "too small" -> List.exists list ~f:(fun x -> Elt.compare x sample < 0)
        | Error "borderline" -> List.exists list ~f:(fun x -> Elt.compare x sample = 0)
        | _ -> false)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    iter_until_

  and[@mode li = (global, l_run), lo = (global, l_run)] fold =
    let fold_ = Impl.fold [@mode li lo] in
    (test_fn [@mode.explicit lo])
      fold_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify, globalize]
      end)
      ~name:[%loc.this_function_name]
      ~description:"elements of the container"
      ~actual:(fun fold container ->
        (fold container ~init:[] ~f:(fun list elt ->
           (elt_smart_globalize [@mode li lo]) elt :: list
           [@exclave_if_local lo ~reasons:[ May_return_local ]])
         |> (list_rev [@mode lo])
         |> (Sort.actual [@mode lo]))
        [@exclave_if_local lo ~reasons:[ May_return_local ]])
      ~expect:(fun container -> Impl.to_list container |> Sort.expect)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    if Config.check_no_allocation
    then
      (test_fn [@mode.explicit global])
        fold_
        (module Cont_with_sample)
        (module Int)
        ~name:[%loc.this_function_name]
        ~description:"balance of comparisons against sample"
        ~actual:(fun fold { container; sample } ->
          fold container ~init:0 ~f:(fun acc x -> acc + (Elt.compare [@mode li]) x sample)
          [@nontail])
        ~expect:(fun { container; sample } ->
          Impl.fold container ~init:0 ~f:(fun n x -> n + Elt.compare x sample))
        ~expect_no_allocation:true;
    fold_

  and[@mode li = (global, l_run), lo = (global, l_run)] fold_result =
    let fold_result_ = Impl.fold_result [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      fold_result_
      (module Cont_with_sample)
      (module struct
        type t = (Elt.t, string) Result.t [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or last element, or sample if empty"
      ~actual:(fun fold_result { container; sample } ->
        fold_result container ~init:sample ~f:(fun _ x ->
          match[@exclave_if_local lo ~reasons:[ May_return_local ]]
            Ordering.of_int ((Elt.compare [@mode li]) x sample)
          with
          | Less -> Error "too small"
          | Equal -> Error "borderline"
          | Greater -> Ok ((elt_smart_globalize [@mode li lo]) x))
        [@nontail] [@exclave_if_local lo ~reasons:[ May_return_local ]])
      ~expect:(fun { container; sample } ->
        List.fold_result (Impl.to_list container) ~init:sample ~f:(fun _ x ->
          match Ordering.of_int (Elt.compare x sample) with
          | Less -> Error "too small"
          | Equal -> Error "borderline"
          | Greater -> Ok x))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | Ok elt ->
          if List.is_empty list
          then (Elt.equal [@mode lo]) elt sample
          else
            (elt_list_mem [@mode lo]) list elt
            && not (List.exists list ~f:(fun x -> Elt.compare x sample <= 0))
        | Error "too small" -> List.exists list ~f:(fun x -> Elt.compare x sample < 0)
        | Error "borderline" -> List.exists list ~f:(fun x -> Elt.compare x sample = 0)
        | _ -> false)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    fold_result_

  and[@mode li = (global, l_run), lo = (global, l_run)] fold_until =
    let fold_until_ = Impl.fold_until [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      fold_until_
      (module Cont_with_sample)
      (module struct
        type t = (Elt.t, string) Result.t [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or last element, or sample if empty"
      ~actual:(fun fold_until { container; sample } ->
        fold_until
          container
          ~init:sample
          ~f:(fun _ x ->
            match[@exclave_if_local lo ~reasons:[ May_return_local ]]
              Ordering.of_int ((Elt.compare [@mode li]) x sample)
            with
            | Less -> Stop (Error "too small")
            | Equal -> Stop (Error "borderline")
            | Greater -> Continue ((elt_smart_globalize [@mode li lo]) x))
          ~finish:(result_return [@mode lo])
        [@nontail] [@exclave_if_local lo ~reasons:[ May_return_local ]])
      ~expect:(fun { container; sample } ->
        List.fold_until
          (Impl.to_list container)
          ~init:sample
          ~f:(fun _ x ->
            match Ordering.of_int (Elt.compare x sample) with
            | Less -> Stop (Error "too small")
            | Equal -> Stop (Error "borderline")
            | Greater -> Continue x)
          ~finish:Result.return [@nontail])
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | Ok elt ->
          if List.is_empty list
          then (Elt.equal [@mode lo]) elt sample
          else
            (elt_list_mem [@mode lo]) list elt
            && not (List.exists list ~f:(fun x -> Elt.compare x sample <= 0))
        | Error "too small" -> List.exists list ~f:(fun x -> Elt.compare x sample < 0)
        | Error "borderline" -> List.exists list ~f:(fun x -> Elt.compare x sample = 0)
        | _ -> false)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    fold_until_

  and[@mode l = (global, l_run)] exists =
    let exists_ = Impl.exists [@mode l] in
    (test_fn [@mode.explicit global])
      exists_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"is there anything less than or equal to the sample"
      ~actual:(fun exists { container; sample } ->
        exists container ~f:(fun x -> (Elt.compare [@mode l]) x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.fold container ~init:false ~f:(fun b x -> b || Elt.compare x sample <= 0))
      ~expect_no_allocation:true;
    exists_

  and[@mode l = (global, l_run)] for_all =
    let for_all_ = Impl.for_all [@mode l] in
    (test_fn [@mode.explicit global])
      for_all_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"is everything less than or equal to the sample"
      ~actual:(fun for_all { container; sample } ->
        for_all container ~f:(fun x -> (Elt.compare [@mode l]) x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.fold container ~init:true ~f:(fun b x -> b && Elt.compare x sample <= 0))
      ~expect_no_allocation:true;
    for_all_

  and[@mode l = (global, l_run)] count =
    let count_ = Impl.count [@mode l] in
    (test_fn [@mode.explicit global])
      count_
      (module Cont_with_sample)
      (module Int)
      ~name:[%loc.this_function_name]
      ~description:"how many elements are less than or equal to the sample"
      ~actual:(fun count { container; sample } ->
        count container ~f:(fun x -> (Elt.compare [@mode l]) x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.fold container ~init:0 ~f:(fun n x ->
          n + Bool.to_int (Elt.compare x sample <= 0)))
      ~expect_no_allocation:true;
    count_

  and[@mode li = (global, l_run), lo = (global, l_run)] sum =
    let sum_ = Impl.sum [@mode li lo] in
    (test_fn [@mode.explicit global])
      sum_
      (module Cont_with_sample)
      (module Int)
      ~name:[%loc.this_function_name]
      ~description:
        "add 1 for elements greater than the sample, and 2 for elements equal to the \
         sample"
      ~actual:(fun sum { container; sample } ->
        sum (module Int) container ~f:(fun x ->
          match Ordering.of_int ((Elt.compare [@mode li]) x sample) with
          | Less -> 0
          | Equal -> 2
          | Greater -> 1)
        [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.count container ~f:(fun x -> Elt.compare x sample >= 0)
        + Impl.count container ~f:(fun x -> Elt.compare x sample = 0))
      ~expect_no_allocation:true;
    sum_

  and[@mode l = (global, l_run)] find =
    let find_ = Impl.find [@mode l] in
    (test_fn_nondeterministic [@mode.explicit l])
      find_
      (module Cont_with_sample)
      (module struct
        type t = Elt.t option [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"first value less than or equal to the sample"
      ~actual:(fun find { container; sample } ->
        find container ~f:(fun x -> (Elt.compare [@mode l]) x sample <= 0)
        [@nontail] [@exclave_if_local l ~reasons:[ May_return_regional ]])
      ~expect:(fun { container; sample } ->
        List.find (Impl.to_list container) ~f:(fun x -> Elt.compare x sample <= 0))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | None -> List.for_all list ~f:(fun x -> (Elt.compare [@mode l]) x sample > 0)
        | Some elt ->
          (Elt.compare [@mode l]) elt sample <= 0 && (elt_list_mem [@mode l]) list elt)
      ~expect_no_allocation:(is_local (mode [@mode l]));
    find_

  and[@mode li = (global, l_run), lo = (global, l_run)] find_map =
    let find_map_ = Impl.find_map [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      find_map_
      (module Cont_with_sample)
      (module struct
        type t = Elt.t list option [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:
        "first value not equal to the sample, listed once if less and twice if greater"
      ~actual:(fun find_map { container; sample } ->
        find_map container ~f:(fun x ->
          let elt_smart_globalize = elt_smart_globalize [@mode li lo] in
          match[@exclave_if_local lo ~reasons:[ May_return_local ]]
            Ordering.of_int ((Elt.compare [@mode li]) x sample)
          with
          | Less -> Some [ elt_smart_globalize x ]
          | Equal -> None
          | Greater -> Some [ elt_smart_globalize x; elt_smart_globalize x ])
        [@nontail] [@exclave_if_local lo ~reasons:[ May_return_local ]])
      ~expect:(fun { container; sample } ->
        List.find_map (Impl.to_list container) ~f:(fun x ->
          match Ordering.of_int (Elt.compare x sample) with
          | Less -> Some [ x ]
          | Equal -> None
          | Greater -> Some [ x; x ]))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | None -> List.for_all list ~f:(fun x -> Elt.compare x sample = 0)
        | Some [ x ] ->
          (Elt.compare [@mode lo]) x sample < 0 && (elt_list_mem [@mode lo]) list x
        | Some [ x; y ] ->
          (Elt.compare [@mode lo]) x sample > 0
          && (Elt.equal [@mode lo]) x y
          && (elt_list_mem [@mode lo]) list x
        | Some ([] | _ :: _ :: _ :: _) -> false)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    find_map_

  and[@alloc a @ l = (heap @ global, a_run @ l_run)] to_list =
    let to_list_ = Impl.to_list [@alloc a] in
    (* Both [to_list] and [fold] are our most direct and complete ways of observing the
       contents of an arbitrary container. We test them against each other in essentially
       the same way. But most other functions are tested against one or the other of them,
       so this redundancy is probably fine, and there's not much of a better way to test
       these two. *)
    (test_fn [@mode.explicit l])
      to_list_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"elements of the container"
      ~actual:(fun to_list container ->
        (to_list container |> (Sort.actual [@mode l])) [@exclave_if_stack a])
      ~expect:(fun container ->
        Impl.fold container ~init:[] ~f:(fun list elt -> elt :: list)
        |> List.rev
        |> Sort.expect)
      ~expect_no_allocation:(is_stack (alloc [@alloc a]));
    to_list_

  and to_array =
    (test_fn [@mode.explicit global])
      Impl.to_array
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"elements of the container"
      ~actual:(fun to_array container -> Sort.actual (Array.to_list (to_array container)))
      ~expect:(fun container ->
        Impl.fold container ~init:[] ~f:(fun array elt -> elt :: array)
        |> List.rev
        |> Sort.expect) (* This case is special: arrays are always global *)
      ~expect_no_allocation:false;
    Impl.to_array

  and[@mode l = (global, l_run)] min_elt =
    let min_elt_ = Impl.min_elt [@mode l] in
    (test_fn [@mode.explicit l])
      min_elt_
      (module Cont)
      (module struct
        type t = Elt.t Option.t [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"the smallest element"
      ~actual:(fun min_elt container ->
        min_elt
          container
          ~compare:(Elt.compare [@mode l]) [@nontail] [@exclave_if_local l])
      ~expect:(fun container ->
        Impl.fold container ~init:None ~f:(fun opt elt ->
          match opt with
          | None -> Some elt
          | Some x -> Some (Comparable.min Elt.compare x elt)))
      ~expect_no_allocation:(is_local (mode [@mode l]));
    min_elt_

  and[@mode l = (global, l_run)] max_elt =
    let max_elt_ = Impl.max_elt [@mode l] in
    (test_fn [@mode.explicit l])
      max_elt_
      (module Cont)
      (module struct
        type t = Elt.t option [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"the largest element"
      ~actual:(fun max_elt container ->
        max_elt
          container
          ~compare:(Elt.compare [@mode l]) [@nontail] [@exclave_if_local l])
      ~expect:(fun container ->
        Impl.fold container ~init:None ~f:(fun opt elt ->
          match opt with
          | None -> Some elt
          | Some x -> Some (Comparable.max Elt.compare x elt)))
      ~expect_no_allocation:(is_local (mode [@mode l]));
    max_elt_
  ;;
end

[%%template
[@@@alloc.default a @ l = (heap_global, stack_local)]

(* Wraps and exports [Run] as a function. *)
let test_container_generic
  ?(cr = CR.CR)
  ?(duplicates = Duplicates.Keep)
  ?(order = Order.Original)
  ?(quickcheck_config = Base_quickcheck.Test.default_config)
  ?(check_no_allocation = false)
  (module Impl : Container_generic[@alloc a])
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
      module type S = Container.Generic [@alloc a]

      module Run () = Run [@alloc a] (Config) (Impl)
    end)
;;

(* Instantiates [test_container_generic] for [Container.S0]. *)
let test_container_s0
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Container_s0[@alloc a])
  =
  (test_container_generic [@alloc a])
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
      end

      type (_, _, _) t = Impl.t

      let%template[@mode l = (global, l)] mem t x ~equal:_ = (Impl.mem [@mode l]) t x
    end)
;;

(* Instantiates [test_container_generic] for [Container.S1]. *)
let test_container_s1
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Container_s1[@alloc a])
  =
  test_container_generic
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
        type 'a t = 'a Impl.t [@@deriving equal, quickcheck, sexp_of]
      end

      type ('a, _, _) t = 'a Impl.t
    end)
;;]
