open! Base
open Base_container_tests_intf.Definitions
open Expect_test_helpers_base

(* Provides test coverage for [Indexed_container.Generic]. *)
module%template
  [@alloc a_run @ l_run = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Indexed_container_generic
  [@alloc a_run])
    (Container_already_tested : Container.Generic
                                [@alloc a_run]
                                with type 'a elt := 'a Impl.Elt.t
                                 and type ('a, 'phantom1, 'phantom2) t :=
                                  ('a, 'phantom1, 'phantom2) Impl.t) =
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

  (* As in [container_tests.ml], we define all tests in a single [let ... and]. *)

  let%template () = ()

  and[@mode li = (global, l_run), lo = (global, l_run)] foldi =
    let foldi_ = Impl.foldi [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      foldi_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify, globalize]
      end)
      ~name:[%loc.this_function_name]
      ~description:"all but the first element"
      ~actual:(fun foldi container ->
        (foldi container ~init:[] ~f:(fun i list sample ->
           if i = 0
           then list
           else
             (elt_smart_globalize [@mode li lo]) sample :: list
             [@exclave_if_local lo ~reasons:[ May_return_local ]])
         |> (list_rev [@mode lo]))
        [@nontail] [@exclave_if_local lo ~reasons:[ May_return_local ]])
      ~expect:(fun container -> List.drop (Impl.to_list container) 1)
      ~expect_if_unpredictable:(fun input output ->
        let input = List.sort ~compare:(Elt.compare [@mode lo]) (Impl.to_list input) in
        let output =
          elt_list_globalize output |> List.sort ~compare:(Elt.compare [@mode lo])
        in
        if List.is_empty input
        then List.is_empty output
        else (
          let[@tail_mod_cons] rec remove list elt =
            match list with
            | [] -> assert false
            | head :: tail -> if Elt.equal head elt then tail else head :: remove tail elt
          in
          List.exists input ~f:(fun elt -> [%equal: Elt.t list] output (remove input elt))))
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    if Config.check_no_allocation
    then
      (test_fn [@mode.explicit global])
        foldi_
        (module Cont_with_sample)
        (module Int)
        ~name:[%loc.this_function_name]
        ~description:"balance of comparisons against sample"
        ~actual:(fun foldi { container; sample } ->
          foldi container ~init:0 ~f:(fun _ acc x ->
            acc + (Elt.compare [@mode li]) x sample)
          [@nontail])
        ~expect:(fun { container; sample } ->
          Impl.fold container ~init:0 ~f:(fun n x -> n + Elt.compare x sample))
        ~expect_no_allocation:true;
    foldi_

  and[@mode li = (global, l_run), lo = (global, l_run)] foldi_until =
    let foldi_until_ = Impl.foldi_until [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      foldi_until_
      (module Cont_with_sample)
      (module struct
        type t = int * (Elt.t, string) Result.t
        [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or last element, or sample if empty"
      ~actual:(fun foldi_until { container; sample } ->
        foldi_until
          container
          ~init:sample
          ~f:(fun i _ x ->
            match[@exclave_if_local lo ~reasons:[ May_return_local ]]
              Ordering.of_int ((Elt.compare [@mode li]) x sample)
            with
            | Less -> Stop (i, Error "too small")
            | Equal -> Stop (i, Error "borderline")
            | Greater -> Continue ((elt_smart_globalize [@mode li lo]) x))
          ~finish:(fun i acc -> (i, Ok acc) [@exclave_if_local lo])
        [@nontail] [@exclave_if_local lo ~reasons:[ May_return_local ]])
      ~expect:(fun { container; sample } ->
        List.foldi_until
          (Impl.to_list container)
          ~init:sample
          ~f:(fun i _ x ->
            match Ordering.of_int (Elt.compare x sample) with
            | Less -> Stop (i, Error "too small")
            | Equal -> Stop (i, Error "borderline")
            | Greater -> Continue x)
          ~finish:(fun i acc -> i, Result.return acc))
      ~expect_if_unpredictable:(fun { container; sample } (_i, output) ->
        let list = Impl.to_list container in
        match output with
        | Ok elt ->
          if List.is_empty list
          then (Elt.equal [@mode lo]) elt sample
          else
            (elt_list_mem [@mode lo]) list elt
            && not (List.exists list ~f:(fun x -> (Elt.compare [@mode lo]) x sample <= 0))
        | Error "too small" ->
          List.exists list ~f:(fun x -> (Elt.compare [@mode lo]) x sample < 0)
        | Error "borderline" ->
          List.exists list ~f:(fun x -> (Elt.compare [@mode lo]) x sample = 0)
        | _ -> false)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    foldi_until_

  and[@mode l = (global, l_run)] iteri =
    let iteri_ = Impl.iteri [@mode l] in
    (test_fn_nondeterministic [@mode.explicit global])
      iteri_
      (module Cont)
      (module struct
        type t = Elt.t list [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"all but the first element"
      ~actual:(fun iteri container ->
        let q = Queue.create () in
        iteri container ~f:(fun i sample ->
          if i > 0 then Queue.enqueue q ((elt_smart_globalize [@mode l global]) sample));
        Queue.to_list q)
      ~expect:(fun container -> List.drop (Impl.to_list container) 1)
      ~expect_if_unpredictable:(fun input output ->
        let input = List.sort ~compare:Elt.compare (Impl.to_list input) in
        let output = List.sort ~compare:Elt.compare output in
        if List.is_empty input
        then List.is_empty output
        else (
          let[@tail_mod_cons] rec remove list elt =
            match list with
            | [] -> assert false
            | head :: tail -> if Elt.equal head elt then tail else head :: remove tail elt
          in
          List.exists input ~f:(fun elt -> [%equal: Elt.t list] output (remove input elt))))
      ~expect_no_allocation:false
    (* This test cannot check for allocation because we allocate the queue *);
    if Config.check_no_allocation
    then
      (test_fn [@mode.explicit global])
        iteri_
        (module Cont_with_sample)
        (module Int)
        ~name:[%loc.this_function_name]
        ~description:"balance of comparisons against sample"
        ~actual:(fun iteri { container; sample } ->
          let r = ref 0 in
          iteri container ~f:(fun _ x -> r := !r + (Elt.compare [@mode l]) x sample)
          [@nontail];
          !r)
        ~expect:(fun { container; sample } ->
          Impl.fold container ~init:0 ~f:(fun n x -> n + (Elt.compare [@mode l]) x sample))
        ~expect_no_allocation:true;
    iteri_

  and[@mode li = (global, l_run), lo = (global, l_run)] iteri_until =
    let iteri_until_ = Impl.iteri_until [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      iteri_until_
      (module Cont_with_sample)
      (module struct
        type t = (int, int * string) Result.t
        [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"error if any <= sample, or Ok if all > sample"
      ~actual:(fun iteri_until { container; sample } ->
        iteri_until
          container
          ~f:(fun i x ->
            match[@exclave_if_local lo ~reasons:[ Will_return_unboxed ]]
              Ordering.of_int ((Elt.compare [@mode li]) x sample)
            with
            | Less -> Stop (Error (i, "too small"))
            | Equal -> Stop (Error (i, "borderline"))
            | Greater -> Continue ())
          ~finish:(result_return [@mode lo])
        [@nontail] [@exclave_if_local lo ~reasons:[ Will_return_unboxed ]])
      ~expect:(fun { container; sample } ->
        List.iteri_until
          (Impl.to_list container)
          ~f:(fun i x ->
            match Ordering.of_int (Elt.compare x sample) with
            | Less -> Stop (Error (i, "too small"))
            | Equal -> Stop (Error (i, "borderline"))
            | Greater -> Continue ())
          ~finish:Result.return)
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | Ok i ->
          i = List.length list
          && not (List.exists list ~f:(fun x -> Elt.compare x sample <= 0))
        | Error (i, "too small") ->
          i < List.length list && List.exists list ~f:(fun x -> Elt.compare x sample < 0)
        | Error (i, "borderline") ->
          i < List.length list && List.exists list ~f:(fun x -> Elt.compare x sample = 0)
        | _ -> false)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    iteri_until_

  and[@mode l = (global, l_run)] existsi =
    let existsi_ = Impl.existsi [@mode l] in
    (test_fn_nondeterministic [@mode.explicit global])
      existsi_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"does the sample occur after the first element"
      ~actual:(fun existsi { container; sample } ->
        existsi container ~f:(fun i x -> i > 0 && (Elt.equal [@mode l]) x sample)
        [@nontail])
      ~expect:(fun { container; sample } ->
        List.mem (List.drop (Impl.to_list container) 1) sample ~equal:Elt.equal)
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | true -> List.exists list ~f:(Elt.equal sample)
        | false -> List.count list ~f:(Elt.equal sample) <= 1)
      ~expect_no_allocation:true;
    existsi_

  and[@mode l = (global, l_run)] for_alli =
    let for_alli_ = Impl.for_alli [@mode l] in
    (test_fn_nondeterministic [@mode.explicit global])
      for_alli_
      (module Cont_with_sample)
      (module Bool)
      ~name:[%loc.this_function_name]
      ~description:"is the sample absent after the first element"
      ~actual:(fun for_alli { container; sample } ->
        for_alli container ~f:(fun i x -> i = 0 || not ((Elt.equal [@mode l]) x sample))
        [@nontail])
      ~expect:(fun { container; sample } ->
        not (List.mem (List.drop (Impl.to_list container) 1) sample ~equal:Elt.equal))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | false -> List.exists list ~f:(Elt.equal sample)
        | true -> List.count list ~f:(Elt.equal sample) <= 1)
      ~expect_no_allocation:true;
    for_alli_

  and[@mode l = (global, l_run)] counti =
    let counti_ = Impl.counti [@mode l] in
    (test_fn_nondeterministic [@mode.explicit global])
      counti_
      (module Cont_with_sample)
      (module Int)
      ~name:[%loc.this_function_name]
      ~description:"how many times does the sample occur after the first element"
      ~actual:(fun counti { container; sample } ->
        counti container ~f:(fun i x -> i > 0 && (Elt.equal [@mode l]) x sample)
        [@nontail])
      ~expect:(fun { container; sample } ->
        List.length
          (List.filter (List.drop (Impl.to_list container) 1) ~f:(Elt.equal sample)))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        let count = List.count list ~f:(Elt.equal sample) in
        count = output || (count > 0 && output = count - 1))
      ~expect_no_allocation:true;
    counti_

  and[@mode l = (global, l_run)] findi =
    let findi_ = Impl.findi [@mode l] in
    (test_fn_nondeterministic [@mode.explicit l])
      findi_
      (module Cont_with_sample)
      (module struct
        type t = (int * Elt.t) option [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"the first value greater than the sample after the first element"
      ~actual:(fun findi { container; sample } ->
        findi container ~f:(fun i x -> i > 0 && (Elt.compare [@mode l]) x sample > 0)
        [@nontail]
        [@exclave_if_local l ~reasons:[ May_return_regional; Will_return_unboxed ]])
      ~expect:(fun { container; sample } ->
        Impl.foldi container ~init:None ~f:(fun i acc x ->
          Option.first_some
            acc
            (Option.some_if (i > 0 && Elt.compare x sample > 0) (i, x))))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | None -> List.count list ~f:(fun x -> (Elt.compare [@mode l]) x sample > 0) <= 1
        | Some (i, x) ->
          i > 0 && (Elt.compare [@mode l]) x sample > 0 && (elt_list_mem [@mode l]) list x)
      ~expect_no_allocation:(is_local (mode [@mode l]));
    findi_

  and[@mode li = (global, l_run), lo = (global, l_run)] find_mapi =
    let find_mapi_ = Impl.find_mapi [@mode li lo] in
    (test_fn_nondeterministic [@mode.explicit lo])
      find_mapi_
      (module Cont_with_sample)
      (module struct
        type t = (int * Elt.t) option [@@deriving equal ~localize, sexp_of ~stackify]
      end)
      ~name:[%loc.this_function_name]
      ~description:"where does the sample occur after the first element"
      ~actual:(fun findi { container; sample } ->
        findi container ~f:(fun i x ->
          (if i > 0 && (Elt.equal [@mode li]) x sample
           then Some (i, (elt_smart_globalize [@mode li lo]) x)
           else None)
          [@exclave_if_local lo ~reasons:[ May_return_regional; Will_return_unboxed ]])
        [@nontail]
        [@exclave_if_local lo ~reasons:[ May_return_regional; Will_return_unboxed ]])
      ~expect:(fun { container; sample } ->
        List.find_mapi (Impl.to_list container) ~f:(fun i x ->
          if i > 0 && Elt.equal x sample then Some (i, x) else None))
      ~expect_if_unpredictable:(fun { container; sample } output ->
        let list = Impl.to_list container in
        match output with
        | None -> List.count list ~f:(Elt.equal sample) <= 1
        | Some (i, x) ->
          i > 0 && (Elt.equal [@mode lo]) x sample && (elt_list_mem [@mode lo]) list x)
      ~expect_no_allocation:(is_local (mode [@mode lo]));
    find_mapi_
  ;;

  (* We [include] previously tested bindings at the end. Previous tests still need to
     refer to [Impl] explicitly for these functions. *)
  include Container_already_tested
end

[%%template
[@@@alloc.default a @ l = (heap_global, stack_local)]

(* Wraps and exports [Run] as a function. *)
let test_indexed_container_generic
  ?(cr = CR.CR)
  ?(duplicates = Duplicates.Keep)
  ?(order = Order.Original)
  ?(quickcheck_config = Base_quickcheck.Test.default_config)
  ?(check_no_allocation = false)
  (module Impl : Indexed_container_generic[@alloc a])
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
      module type S = Indexed_container.Generic [@alloc a]

      module Run () = struct
        open struct
          module Container = Container_tests.Run [@alloc a] (Config) (Impl)
        end

        include Run [@alloc a] (Config) (Impl) (Container)
      end
    end)
;;

(* Instantiates [test_indexed_container_generic] for [Indexed_container.S0]. *)
let test_indexed_container_s0
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Indexed_container_s0[@alloc a])
  =
  (test_indexed_container_generic [@alloc a])
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

(* Instantiates [test_indexed_container_generic] for [Indexed_container.S1]. *)
let test_indexed_container_s1
  ?cr
  ?duplicates
  ?order
  ?quickcheck_config
  ?check_no_allocation
  (module Impl : Indexed_container_s1[@alloc a])
  =
  (test_indexed_container_generic [@alloc a])
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
      end

      type ('a, _, _) t = 'a Impl.t
    end)
;;]
