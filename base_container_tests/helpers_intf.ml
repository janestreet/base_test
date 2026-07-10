(** Helpers for constructing tests of container interfaces. *)

open! Base
open Base_container_tests_intf.Definitions
open Expect_test_helpers_base

module Definitions = struct
  (** [Config] determines how expect tests are run. *)
  module type Config = sig
    val cr : CR.t
    val duplicates : Duplicates.t
    val order : Order.t
    val quickcheck_config : Base_quickcheck.Test.Config.t
    val check_no_allocation : bool
  end

  (** [Coverage] describes a module that tests all exports in some signature [S]. [Run] is
      a generative functor that, when instantiated, runs expect tests. By having [Run]
      provide [S], the compiler will complain if the user has not added some export, which
      should in turn prompt them to test it. *)
  module type Coverage = sig
    module type S

    (** Runs expect tests for functions in [S]. Should be run using [test_m], below. *)
    module Run () : S
  end

  (** [Testable] describes how to generate, compare, and serialize containers and
      elements. This is the input to the [Test] module below. *)
  module type%template [@alloc a @ l = (heap_global, stack_local)] Testable = sig
    module Elt : sig
      type 'a t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    module Cont : sig
      type 'a t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]
    end

    module Concat : sig
      type 'a t

      val to_list : 'a t -> 'a list
      val of_list : 'a list -> 'a t
    end
  end

  module type%template [@mode global] Output = sig
    type t : any [@@deriving equal, sexp_of]
  end

  module type%template [@mode local] Output = sig
    type t : any [@@deriving equal ~localize, sexp_of ~stackify]
  end

  (** [Test] provides helpers for building quickcheck expect tests. Use these when
      constructing an instance of [Coverage], above. *)
  module type%template [@alloc a @ l = (heap_global, stack_local)] Test = sig
    type 'a elt
    type 'a container
    type 'a concat

    module Elt : sig
      type t = int elt
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    module Cont : sig
      type t = int container
      [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]
    end

    (** We often want to test a function using a container, and some element to operate on
        the container. We could insert the sample, remove it, filter out anything less
        than it, etc. We define the pair as a record so that sexps are explicit. *)
    module Cont_with_sample : sig
      type t =
        { container : Cont.t
        ; sample : Elt.t
        }
      [@@deriving quickcheck, sexp_of]
    end

    module Concat : sig
      type t = Cont.t concat [@@deriving equal, quickcheck, sexp_of]

      val to_list : t -> Cont.t list
      val of_list : Cont.t list -> t
    end

    module Sort : sig
      (** Sort "actual" results, i.e. the output of a container traversal. Specifically,
          if the container produces unpredictable ordering, sort the elements in ascending
          order. Otherwise, does nothing. *)
      val%template actual : Elt.t list @ l -> Elt.t list @ l
      [@@mode l = (local, global)]

      (** Sort "expected" results, i.e. the output of a reference implementation. Removes
          duplicates and/or sorts elements so the output is consistent with what
          [Sort.actual] of the actual output should provide. *)
      val expect : Elt.t list -> Elt.t list
    end

    (* In some cases, tests globalize to return a global element from a local one. [glob]
       is necessary to ensure that when globalizes are needed conditionally, we can
       instantiate a smart globalize that would not allocate when it is not necessary
       (e.g. local-local or global-global). This in turn is necessary so that we can test
       that functions do not allocate. *)

    (** Helpers for support of containers templated across locality *)
    module%template Locality : sig
      (* These are necessary to do some conditional logic on whether a test, as
         instantiated from a template, should test for no allocations *)
      type mode =
        | Global
        | Local

      type alloc =
        | Heap
        | Stack

      val mode : mode [@@mode l = (global, local)]
      val alloc : alloc [@@alloc a = (heap, stack)]

      (** Used when a test expects not to allocate only when it returns a [local]. *)
      val is_local : mode -> bool

      (** Used when a test expects not to allocate when using a [stack] allocator. *)
      val is_stack : alloc -> bool

      val smart_globalize : ('a @ local -> 'a) -> 'a @ li -> 'a @ lo
      [@@mode li = (global, l), lo = (global, l)]

      (** Short-hand for [List.globalize Elt.globalize] *)
      val elt_list_globalize : local_ Elt.t list -> Elt.t list

      val elt_smart_globalize : Elt.t @ li -> Elt.t @ lo
      [@@mode li = (global, l), lo = (global, l)]

      (** Short-hand for templated-instantiated [List.mem] with [Elt.equal] *)
      val elt_list_mem : Elt.t list @ l -> Elt.t @ l -> bool
      [@@mode l = (global, l)]

      (* These helpers are necessary in tests that only template by mode, as underlying
         functions would template by alloc *)
      val list_rev : 'a list @ l -> 'a list @ l [@@mode l = (global, local)]
      val result_return : 'a @ l -> ('a, 'b) result @ l [@@mode l = (global, local)]
    end

    (** When testing a function, provide the following:

        - The function to test, of type ['fn]
        - A module describing the input type, ['input]
        - A module describing the result type, ['output]
        - The [name] of the function
        - A [description] of what the function computes
        - A function computing the [actual] result of the function
        - A function computing the [expect]ed result of the function

        Usually [actual] is trivial. It is provided in case [fn] needs to be wrapped, such
        as to put a label on a named argument, or to wrap the function in
        [Or_error.try_with] to test a function that may raise.

        The [expect] function should be a reference implementation of [actual], such as
        implementing [is_empty] in terms of [length]. It is not passed [fn]; this is a
        hint that it should not call [fn].

        [test_fn] runs a test that prints the name of the function being tested. This is
        followed by any test failures, annotated with [description]. When used for every
        function passed to [test_m], you get a list of the functions that have been tested
        so that it is at least clear the test did something. *)
    val test_fn
      :  'fn
      -> (module Base_quickcheck.Test.S with type t = 'input)
      -> ((module Output with type t = 'output)[@mode l])
      -> name:string
      -> description:string
      -> actual:('fn -> 'input -> 'output @ l)
      -> expect:('input -> 'output)
      -> expect_no_allocation:bool
      -> unit
    [@@mode.explicit l = (global, l)]

    (** Like [test_fn]; runs [expect_if_unpredictable] if the output for a container with
        unpredictable ordering cannot simply be compared against a reference value. *)
    val test_fn_nondeterministic
      :  'fn
      -> (module Base_quickcheck.Test.S with type t = 'input)
      -> ((module Output with type t = 'output)[@mode l])
      -> name:string
      -> description:string
      -> actual:('fn -> 'input -> 'output @ l)
      -> expect:('input -> 'output)
      -> expect_if_unpredictable:('input -> 'output @ l -> bool)
      -> expect_no_allocation:bool
      -> unit
    [@@mode.explicit l = (global, l)]
  end
end

module type Helpers = sig
  include module type of struct
    include Definitions
  end

  (** Runs expect tests that cover some signature's exports. Raises if run outside an
      expect test, so that output is not inadvertently thrown away. *)
  val test_m : (module Coverage) -> unit

  (** Provides an instance of [Test]. Instantiate when implementing [Coverage]. *)
  module%template
    [@alloc a @ l = (heap_global, stack_local)] Test
      (Config : Config)
      (Testable : Testable
    [@alloc a]) :
    Test
    [@alloc a]
    with type 'a elt := 'a Testable.Elt.t
     and type 'a container := 'a Testable.Cont.t
     and type 'a concat := 'a Testable.Concat.t
end
