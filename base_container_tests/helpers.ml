open! Base
open Base_quickcheck.Export
open Expect_test_helpers_base
include Helpers_intf.Definitions

let test_m (module Coverage : Coverage) =
  assert_am_running_expect_test ();
  let module _ : Coverage.S = Coverage.Run () in
  ()
;;

module Test (Config : Config) (Testable : Testable) = struct
  (* Define an integer generated using small non-negative values. This makes good testing
     inputs, as it will frequently generate duplicate or similar values, rather than
     things that are all over the place. *)
  module Nat = struct
    type t = (int[@generator Base_quickcheck.Generator.small_positive_or_zero_int])
    [@@deriving compare, equal, quickcheck, sexp_of, globalize]
  end

  module Elt = struct
    type t = Nat.t Testable.Elt.t
    [@@deriving compare, equal, quickcheck, sexp_of, globalize]
  end

  module Cont = struct
    type t = Nat.t Testable.Cont.t [@@deriving equal, quickcheck, sexp_of]
  end

  module Concat = struct
    type t = Cont.t Testable.Concat.t

    let to_list = Testable.Concat.to_list
    let of_list = Testable.Concat.of_list
    let equal x y = [%equal: Cont.t list] (to_list x) (to_list y) [@nontail]
    let equal = equal
    let sexp_of_t t = [%sexp_of: Cont.t list] (to_list t)

    open Base_quickcheck

    let quickcheck_generator = [%generator: Cont.t list] |> Generator.map ~f:of_list
    let quickcheck_observer = [%observer: Cont.t list] |> Observer.unmap ~f:to_list

    let quickcheck_shrinker =
      [%shrinker: Cont.t list] |> Shrinker.map ~f:of_list ~f_inverse:to_list
    ;;
  end

  module Cont_with_sample = struct
    type t =
      { container : Cont.t
      ; sample : Elt.t
      }
    [@@deriving quickcheck, sexp_of]
  end

  module Sort = struct
    (* The specialisation hack is necessary to allow [Sort] to be used by tests (thus,
       container functions) that are not templated by [alloc]. *)

    let actual_alloc =
      match Config.order with
      | Original | Sorted -> Fn.id
      | Unpredictable -> List.stable_sort ~compare:Elt.compare
    ;;

    let actual = actual_alloc

    let expect =
      let order =
        match Config.order with
        | Original -> Fn.id
        | Sorted | Unpredictable -> List.stable_sort ~compare:Elt.compare
      in
      let duplicates =
        match Config.duplicates with
        | Keep -> Fn.id
        | Drop -> List.stable_dedup ~compare:Elt.compare
      in
      Fn.compose order duplicates
    ;;
  end

  module Locality = struct
    type mode =
      | Global
      | Local

    type alloc =
      | Heap
      | Stack

    let mode = Global
    let alloc = Heap

    let is_local = function
      | Local -> true
      | Global -> false
    ;;

    let is_stack = function
      | Stack -> true
      | Heap -> false
    ;;

    (* Smart globalize *)
    let smart_globalize _ x = x
    let _, _, _, _ = smart_globalize, smart_globalize, smart_globalize, smart_globalize
    let elt_list_globalize = List.globalize Elt.globalize
    let elt_smart_globalize elt = smart_globalize Elt.globalize elt
    let elt_list_mem list elt = List.mem list elt ~equal:Elt.equal
    let list_rev = List.rev
    let result_return x = Ok x
  end

  include (
  struct
    let sexp_of_output (type output) (module Output : Output with type t = output) output =
      Sexp.globalize (Output.sexp_of_t output) [@nontail]
    ;;
  end :
  sig
    val sexp_of_output : (module Output with type t = 'output) -> 'output -> Sexp.t
  end)

  exception Unexpected_allocation of int

  (* Based on [Test_iarray] *)
  let gc_allocation_check_overhead_in_bytes =
    let count1 = Stdlib.Gc.allocated_bytes () in
    let count2 = Stdlib.Gc.allocated_bytes () in
    count2 -. count1
  ;;

  let words_gc_allocated_between ~bytes_before ~bytes_after =
    let word_size_in_bytes = Sys.word_size_in_bits / 8 in
    Int.of_float (bytes_after -. bytes_before -. gc_allocation_check_overhead_in_bytes)
    / word_size_in_bytes
  ;;

  let test_no_allocation ~expect_no_allocation fn =
    match Config.check_no_allocation && expect_no_allocation with
    | true ->
      let bytes_before = Stdlib.Gc.allocated_bytes () in
      let fn_result = fn () in
      let bytes_after = Stdlib.Gc.allocated_bytes () in
      let words_gc_allocated = words_gc_allocated_between ~bytes_before ~bytes_after in
      assert (words_gc_allocated >= 0);
      if words_gc_allocated > 0 then raise (Unexpected_allocation words_gc_allocated);
      fn_result
    | false -> fn ()
  ;;

  let test_fn_nondeterministic_internal
    (type output)
    fn
    input_m
    output_m
    ~name
    ~description
    ~actual
    ~expect
    ~expect_if_unpredictable
    ~expect_no_allocation
    =
    let expect_no_allocation = Config.check_no_allocation && expect_no_allocation in
    let (module Output : Output with type t = output) = output_m in
    print_endline
      (Printf.sprintf
         "Container: testing [%s%s]"
         name
         (if expect_no_allocation then " zero_alloc" else ""));
    quickcheck_m ~config:Config.quickcheck_config ~cr:Config.cr input_m ~f:(fun input ->
      match expect input with
      | exception exn -> print_cr ~cr:Config.cr [%message "[expect] raised" (exn : exn)]
      | expect ->
        (match test_no_allocation ~expect_no_allocation (fun () -> actual fn input) with
         | exception Unexpected_allocation n_words ->
           print_cr
             ~cr:Config.cr
             ~hide_positions:true
             [%message "[actual] allocated" (n_words : int)]
         | exception exn ->
           print_cr
             ~cr:Config.cr
             [%message "[actual] raised" (exn : exn) (expect : Output.t)]
         | actual ->
           print_cr_if_false
             ~cr:Config.cr
             (match Config.order, expect_if_unpredictable with
              | (Original | Sorted), _ | Unpredictable, None -> Output.equal actual expect
              | Unpredictable, Some expect_if_unpredictable ->
                expect_if_unpredictable input actual)
             (fun () ->
               let inconsistency =
                 if Output.equal actual expect
                 then
                   Some
                     [%message "[actual] = [expect] but [expect_if_unpredictable] failed"]
                 else None
               in
               (* Factoring this out is necessary because [actual] is [@ local], and
                  mostly easier than messing with [@message__stack]. *)
               let actual_sexp = sexp_of_output (module Output) actual in
               [%message
                 description
                   (expect : Output.t)
                   ~actual:(actual_sexp : Sexp.t)
                   (inconsistency : (Sexp.t option[@sexp.option]))]) [@nontail]))
  ;;

  let test_fn_nondeterministic
    fn
    input_m
    output_m
    ~name
    ~description
    ~actual
    ~expect
    ~expect_if_unpredictable
    ~expect_no_allocation
    =
    test_fn_nondeterministic_internal
      fn
      input_m
      output_m
      ~name
      ~description
      ~actual
      ~expect
      ~expect_if_unpredictable:(Some expect_if_unpredictable)
      ~expect_no_allocation
  ;;

  let test_fn fn input_m output_m ~name ~description ~actual ~expect ~expect_no_allocation
    =
    test_fn_nondeterministic_internal
      fn
      input_m
      output_m
      ~name
      ~description
      ~actual
      ~expect
      ~expect_if_unpredictable:None
      ~expect_no_allocation
  ;;
end
