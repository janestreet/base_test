open! Base
open Base_container_tests_intf.Definitions
open Expect_test_helpers_base

(* Provides test coverage for [Container.Generic]. *)
module Run (Config : Helpers.Config) (Impl : Container_generic) = struct
  type 'a elt = 'a Impl.Elt.t
  type ('a, 'phantom1, 'phantom2) t = ('a, 'phantom1, 'phantom2) Impl.t

  (* We instantiate helpers for testing [Impl]. *)
  open
    Helpers.Test
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
    test_fn
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
    test_fn
      is_empty_
      (module Cont)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"is the container empty"
      ~actual:(fun is_empty t -> is_empty t)
      ~expect:(fun t -> Impl.length t = 0)
      ~expect_no_allocation:true;
    is_empty_

  and mem =
    let mem_ = Impl.mem in
    test_fn
      mem_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"does the container include the sample"
      ~actual:(fun mem { container; sample } -> mem container sample ~equal:Elt.equal)
      ~expect:(fun { container; sample } ->
        Impl.exists container ~f:(Elt.equal sample) [@nontail])
      ~expect_no_allocation:true;
    mem_

  and iter =
    let iter_ = Impl.iter in
    test_fn
      iter_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"elements of the container"
      ~actual:(fun iter container ->
        let q = Queue.create () in
        iter container ~f:(fun elt -> Queue.enqueue q (elt_smart_globalize elt));
        Sort.actual (Queue.to_list q))
      ~expect:(fun container -> Sort.expect (Impl.to_list container))
      ~expect_no_allocation:false
    (* This test cannot check for allocation because we allocate the queue *);
    if Config.check_no_allocation
    then
      test_fn
        iter_
        (module Cont_with_sample)
        (module Int)
        ~name:[%loc.this_function_name]
        ~description:"balance of comparisons against sample"
        ~actual:(fun iter { container; sample } ->
          let r = ref 0 in
          iter container ~f:(fun x -> r := !r + Elt.compare x sample) [@nontail];
          !r)
        ~expect:(fun { container; sample } ->
          Impl.fold container ~init:0 ~f:(fun n x -> n + Elt.compare x sample))
        ~expect_no_allocation:true;
    iter_

  and iter_until =
    let iter_until_ = Impl.iter_until in
    test_fn_nondeterministic
      iter_until_
      (module Cont_with_sample)
      (module struct
        type t = (unit, string) Result.t [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or Ok if all > sample"
      ~actual:(fun iter_until { container; sample } ->
        iter_until
          container
          ~f:(fun x ->
            match Ordering.of_int (Elt.compare x sample) with
            | Less -> Stop (Error "too small")
            | Equal -> Stop (Error "borderline")
            | Greater -> Continue ())
          ~finish:result_return [@nontail])
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
      ~expect_no_allocation:(is_local mode);
    iter_until_

  and fold =
    let fold_ = Impl.fold in
    test_fn
      fold_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal, sexp_of, globalize]
      end)
      ~name:[%loc.this_function_name]
      ~description:"elements of the container"
      ~actual:(fun fold container ->
        fold container ~init:[] ~f:(fun list elt -> elt_smart_globalize elt :: list)
        |> list_rev
        |> Sort.actual)
      ~expect:(fun container -> Impl.to_list container |> Sort.expect)
      ~expect_no_allocation:(is_local mode);
    if Config.check_no_allocation
    then
      test_fn
        fold_
        (module Cont_with_sample)
        (module Int)
        ~name:[%loc.this_function_name]
        ~description:"balance of comparisons against sample"
        ~actual:(fun fold { container; sample } ->
          fold container ~init:0 ~f:(fun acc x -> acc + Elt.compare x sample) [@nontail])
        ~expect:(fun { container; sample } ->
          Impl.fold container ~init:0 ~f:(fun n x -> n + Elt.compare x sample))
        ~expect_no_allocation:true;
    fold_

  and fold_result =
    let fold_result_ = Impl.fold_result in
    test_fn_nondeterministic
      fold_result_
      (module Cont_with_sample)
      (module struct
        type t = (Elt.t, string) Result.t [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or last element, or sample if empty"
      ~actual:(fun fold_result { container; sample } ->
        fold_result container ~init:sample ~f:(fun _ x ->
          match Ordering.of_int (Elt.compare x sample) with
          | Less -> Error "too small"
          | Equal -> Error "borderline"
          | Greater -> Ok (elt_smart_globalize x))
        [@nontail])
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
          then Elt.equal elt sample
          else
            elt_list_mem list elt
            && not (List.exists list ~f:(fun x -> Elt.compare x sample <= 0))
        | Error "too small" -> List.exists list ~f:(fun x -> Elt.compare x sample < 0)
        | Error "borderline" -> List.exists list ~f:(fun x -> Elt.compare x sample = 0)
        | _ -> false)
      ~expect_no_allocation:(is_local mode);
    fold_result_

  and fold_until =
    let fold_until_ = Impl.fold_until in
    test_fn_nondeterministic
      fold_until_
      (module Cont_with_sample)
      (module struct
        type t = (Elt.t, string) Result.t [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or last element, or sample if empty"
      ~actual:(fun fold_until { container; sample } ->
        fold_until
          container
          ~init:sample
          ~f:(fun _ x ->
            match Ordering.of_int (Elt.compare x sample) with
            | Less -> Stop (Error "too small")
            | Equal -> Stop (Error "borderline")
            | Greater -> Continue (elt_smart_globalize x))
          ~finish:result_return [@nontail])
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
          then Elt.equal elt sample
          else
            elt_list_mem list elt
            && not (List.exists list ~f:(fun x -> Elt.compare x sample <= 0))
        | Error "too small" -> List.exists list ~f:(fun x -> Elt.compare x sample < 0)
        | Error "borderline" -> List.exists list ~f:(fun x -> Elt.compare x sample = 0)
        | _ -> false)
      ~expect_no_allocation:(is_local mode);
    fold_until_

  and exists =
    let exists_ = Impl.exists in
    test_fn
      exists_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"is there anything less than or equal to the sample"
      ~actual:(fun exists { container; sample } ->
        exists container ~f:(fun x -> Elt.compare x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.fold container ~init:false ~f:(fun b x -> b || Elt.compare x sample <= 0))
      ~expect_no_allocation:true;
    exists_

  and for_all =
    let for_all_ = Impl.for_all in
    test_fn
      for_all_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"is everything less than or equal to the sample"
      ~actual:(fun for_all { container; sample } ->
        for_all container ~f:(fun x -> Elt.compare x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.fold container ~init:true ~f:(fun b x -> b && Elt.compare x sample <= 0))
      ~expect_no_allocation:true;
    for_all_

  and count =
    let count_ = Impl.count in
    test_fn
      count_
      (module Cont_with_sample)
      (module Int)
      ~name:[%loc.this_function_name]
      ~description:"how many elements are less than or equal to the sample"
      ~actual:(fun count { container; sample } ->
        count container ~f:(fun x -> Elt.compare x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.fold container ~init:0 ~f:(fun n x ->
          n + Bool.to_int (Elt.compare x sample <= 0)))
      ~expect_no_allocation:true;
    count_

  and sum =
    let sum_ = Impl.sum in
    test_fn
      sum_
      (module Cont_with_sample)
      (module Int)
      ~name:[%loc.this_function_name]
      ~description:
        "add 1 for elements greater than the sample, and 2 for elements equal to the \
         sample"
      ~actual:(fun sum { container; sample } ->
        sum (module Int) container ~f:(fun x ->
          match Ordering.of_int (Elt.compare x sample) with
          | Less -> 0
          | Equal -> 2
          | Greater -> 1)
        [@nontail])
      ~expect:(fun { container; sample } ->
        Impl.count container ~f:(fun x -> Elt.compare x sample >= 0)
        + Impl.count container ~f:(fun x -> Elt.compare x sample = 0))
      ~expect_no_allocation:true;
    sum_

  and find =
    let find_ = Impl.find in
    test_fn_nondeterministic
      find_
      (module Cont_with_sample)
      (module struct
        type t = Elt.t option [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"first value less than or equal to the sample"
      ~actual:(fun find { container; sample } ->
        find container ~f:(fun x -> Elt.compare x sample <= 0) [@nontail])
      ~expect:(fun { container; sample } ->
        List.find (Impl.to_list container) ~f:(fun x -> Elt.compare x sample <= 0))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | None -> List.for_all list ~f:(fun x -> Elt.compare x sample > 0)
        | Some elt -> Elt.compare elt sample <= 0 && elt_list_mem list elt)
      ~expect_no_allocation:(is_local mode);
    find_

  and find_map =
    let find_map_ = Impl.find_map in
    test_fn_nondeterministic
      find_map_
      (module Cont_with_sample)
      (module struct
        type t = Elt.t list option [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:
        "first value not equal to the sample, listed once if less and twice if greater"
      ~actual:(fun find_map { container; sample } ->
        find_map container ~f:(fun x ->
          let elt_smart_globalize = elt_smart_globalize in
          match Ordering.of_int (Elt.compare x sample) with
          | Less -> Some [ elt_smart_globalize x ]
          | Equal -> None
          | Greater -> Some [ elt_smart_globalize x; elt_smart_globalize x ])
        [@nontail])
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
        | Some [ x ] -> Elt.compare x sample < 0 && elt_list_mem list x
        | Some [ x; y ] ->
          Elt.compare x sample > 0 && Elt.equal x y && elt_list_mem list x
        | Some ([] | _ :: _ :: _ :: _) -> false)
      ~expect_no_allocation:(is_local mode);
    find_map_

  and to_list =
    let to_list_ = Impl.to_list in
    (* Both [to_list] and [fold] are our most direct and complete ways of observing the
       contents of an arbitrary container. We test them against each other in essentially
       the same way. But most other functions are tested against one or the other of them,
       so this redundancy is probably fine, and there's not much of a better way to test
       these two. *)
    test_fn
      to_list_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"elements of the container"
      ~actual:(fun to_list container -> to_list container |> Sort.actual)
      ~expect:(fun container ->
        Impl.fold container ~init:[] ~f:(fun list elt -> elt :: list)
        |> List.rev
        |> Sort.expect)
      ~expect_no_allocation:(is_stack alloc);
    to_list_

  and to_array =
    test_fn
      Impl.to_array
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal, sexp_of]
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

  and min_elt =
    let min_elt_ = Impl.min_elt in
    test_fn
      min_elt_
      (module Cont)
      (module struct
        type t = Elt.t Option.t [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"the smallest element"
      ~actual:(fun min_elt container -> min_elt container ~compare:Elt.compare [@nontail])
      ~expect:(fun container ->
        Impl.fold container ~init:None ~f:(fun opt elt ->
          match opt with
          | None -> Some elt
          | Some x -> Some (Comparable.min Elt.compare x elt)))
      ~expect_no_allocation:(is_local mode);
    min_elt_

  and max_elt =
    let max_elt_ = Impl.max_elt in
    test_fn
      max_elt_
      (module Cont)
      (module struct
        type t = Elt.t option [@@deriving equal, sexp_of]
      end)
      ~name:[%loc.this_function_name]
      ~description:"the largest element"
      ~actual:(fun max_elt container -> max_elt container ~compare:Elt.compare [@nontail])
      ~expect:(fun container ->
        Impl.fold container ~init:None ~f:(fun opt elt ->
          match opt with
          | None -> Some elt
          | Some x -> Some (Comparable.max Elt.compare x elt)))
      ~expect_no_allocation:(is_local mode);
    max_elt_
  ;;
end

(* Wraps and exports [Run] as a function. *)
let test_container_generic
  ?(cr = CR.CR)
  ?(duplicates = Duplicates.Keep)
  ?(order = Order.Original)
  ?(quickcheck_config = Base_quickcheck.Test.default_config)
  ?(check_no_allocation = false)
  (module Impl : Container_generic)
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
      module type S = Container.Generic

      module Run () = Run (Config) (Impl)
    end)
;;

(* Instantiates [test_container_generic] for [Container.S0]. *)
let test_container_s0
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Container_s0)
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
        type _ t = Impl.Elt.t [@@deriving compare, equal, quickcheck, sexp_of, globalize]
      end

      module Simple = struct
        type phantom1 = Nothing.t
        type phantom2 = Nothing.t
        type _ t = Impl.t [@@deriving equal, quickcheck, sexp_of]
      end

      type (_, _, _) t = Impl.t

      let mem t x ~equal:_ = Impl.mem t x
    end)
;;

(* Instantiates [test_container_generic] for [Container.S1]. *)
let test_container_s1
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Container_s1)
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
        type 'a t = 'a [@@deriving compare, equal, quickcheck, sexp_of, globalize]
      end

      module Simple = struct
        type phantom1 = Nothing.t
        type phantom2 = Nothing.t
        type 'a t = 'a Impl.t [@@deriving equal, quickcheck, sexp_of]
      end

      type ('a, _, _) t = 'a Impl.t
    end)
;;
