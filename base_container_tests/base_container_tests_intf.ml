(** This file defines signatures used for testing container implementations. We extend
    various [Container] and [Indexed_container] interfaces with deriving clauses like
    [quickcheck] and [sexp_of]. Then we provide functions that run expect tests on
    instances of these signatures.

    By default, the tests assume that all functions traverse elements in the order they
    are provided to [of_list], including duplicates. The [~order] and [~duplicates]
    arguments can be used to override this assumption.

    See the "test" directory for examples of using these tests. *)

open! Base
open Expect_test_helpers_base

module Definitions = struct
  (** Specifies whether a container implementation preserves duplicate elements. *)
  module Duplicates = struct
    type t =
      | Drop (** drop duplicate elements, keeping only one of each value *)
      | Keep (** default: keep all elements, including duplicates *)
    [@@deriving compare, enumerate, equal, sexp_of]
  end

  (** Specifies the order in which a container implementation traverses elements. *)
  module Order = struct
    type t =
      | Original (** default: traverse in order provided to [of_list] *)
      | Sorted (** traverse elements in sorted order *)
      | Unpredictable (** traverse elements in a potentially nondeterministic order *)
    [@@deriving compare, enumerate, equal, sexp_of]
  end

  type 'a test =
    ?cr:CR.t
    -> ?duplicates:Duplicates.t
    -> ?order:Order.t
    -> ?quickcheck_config:Base_quickcheck.Test.Config.t
    -> ?check_no_allocation:bool
    -> 'a
    -> unit

  (** Monomorphic containers with a hard-coded [Elt] type. *)

  module type%template [@alloc a @ l = (heap_global, stack_local)] Container_s0 = sig
    module Elt : sig
      type t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include Container.S0 [@alloc a] with type elt := Elt.t and type t := t
  end

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Indexed_container_s0 = sig
    module Elt : sig
      type t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include Indexed_container.S0 [@alloc a] with type elt := Elt.t and type t := t
  end

  (** Monomorphic containers with creator functions. *)

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Container_s0_with_creators = sig
    module Elt : sig
      type t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include Container.S0_with_creators [@alloc a] with type elt := Elt.t and type t := t
  end

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Indexed_container_s0_with_creators = sig
    module Elt : sig
      type t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include
      Indexed_container.S0_with_creators [@alloc a] with type elt := Elt.t and type t := t
  end

  (** Polymorphic containers with arbitrary element types. *)

  module type%template [@alloc a @ l = (heap_global, stack_local)] Container_s1 = sig
    type 'a t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include Container.S1 [@alloc a] with type 'a t := 'a t
  end

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Indexed_container_s1 = sig
    type 'a t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include Indexed_container.S1 [@alloc a] with type 'a t := 'a t
  end

  (** Polymorphic containers with creator functions. *)

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Container_s1_with_creators = sig
    type 'a t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include Container.S1_with_creators [@alloc a] with type 'a t := 'a t
  end

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Indexed_container_s1_with_creators = sig
    type 'a t [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

    include Indexed_container.S1_with_creators [@alloc a] with type 'a t := 'a t
  end

  (** Generic interfaces that subsume monomorphic, polymorphic, and phantom-typed
      containers. They derive values for a [Simple] container type that hard-codes a
      specific [phantom] type for testing. *)

  module type%template [@alloc a @ l = (heap_global, stack_local)] Container_generic = sig
    module Elt : sig
      type 'a t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type ('a, 'phantom1, 'phantom2) t
    type ('a, 'phantom1, 'phantom2) container := ('a, 'phantom1, 'phantom2) t

    include
      Container.Generic
      [@alloc a]
      with type 'a elt := 'a Elt.t
       and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) t

    module Simple : sig
      type phantom1
      type phantom2

      type 'a t = ('a, phantom1, phantom2) container
      [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]
    end
  end

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Indexed_container_generic = sig
    module Elt : sig
      type 'a t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type ('a, 'phantom1, 'phantom2) t
    type ('a, 'phantom1, 'phantom2) container := ('a, 'phantom1, 'phantom2) t

    include
      Indexed_container.Generic
      [@alloc a]
      with type 'a elt := 'a Elt.t
       and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) t

    module Simple : sig
      type phantom1
      type phantom2

      type 'a t = ('a, phantom1, phantom2) container
      [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]
    end
  end

  (** Generic interfaces with creator functions. They add a [Concat] type used as the
      input to [concat]. *)

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Container_generic_with_creators = sig
    module Elt : sig
      type 'a t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type ('a, 'phantom1, 'phantom2) concat
    type ('a, 'phantom1, 'phantom2) t
    type ('a, 'phantom1, 'phantom2) container := ('a, 'phantom1, 'phantom2) t

    include
      Container.Generic_with_creators
      [@alloc a]
      with type 'a elt := 'a Elt.t
       and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) t
       and type ('a, 'p1, 'p2) concat := ('a, 'p1, 'p2) concat

    module Simple : sig
      type phantom1
      type phantom2

      type 'a t = ('a, phantom1, phantom2) container
      [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

      module Concat : sig
        type 'a t = ('a, phantom1, phantom2) concat
        [@@deriving equal, quickcheck, sexp_of]

        val to_list : 'a t -> 'a list
        val of_list : 'a list -> 'a t
      end
    end
  end

  module type%template
    [@alloc a @ l = (heap_global, stack_local)] Indexed_container_generic_with_creators = sig
    module Elt : sig
      type 'a t
      [@@deriving
        compare ~localize, equal ~localize, quickcheck, sexp_of ~stackify, globalize]
    end

    type ('a, 'phantom1, 'phantom2) t
    type ('a, 'phantom1, 'phantom2) container := ('a, 'phantom1, 'phantom2) t

    include
      Indexed_container.Generic_with_creators
      [@alloc a]
      with type 'a elt := 'a Elt.t
       and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) t

    module Simple : sig
      type phantom1
      type phantom2

      type 'a t = ('a, phantom1, phantom2) container
      [@@deriving (equal [@mode l]), quickcheck, (sexp_of [@alloc a])]

      module Concat : sig
        type 'a t = ('a, phantom1, phantom2) concat
        [@@deriving equal, quickcheck, sexp_of]

        val to_list : 'a t -> 'a list
        val of_list : 'a list -> 'a t
      end
    end
  end

  (** Testing functions for containers. *)

  module type Container_tests = sig
    [%%template:
    [@@@alloc.default a = (heap, stack)]

    val test_container_s0 : ((module Container_s0)[@alloc a]) test
    val test_container_s1 : ((module Container_s1)[@alloc a]) test
    val test_container_generic : ((module Container_generic)[@alloc a]) test]
  end

  module type Indexed_container_tests = sig
    [%%template:
    [@@@alloc.default a = (heap, stack)]

    val test_indexed_container_s0 : ((module Indexed_container_s0)[@alloc a]) test
    val test_indexed_container_s1 : ((module Indexed_container_s1)[@alloc a]) test

    val test_indexed_container_generic
      : ((module Indexed_container_generic)[@alloc a]) test]
  end

  (** Testing functions including creators. *)

  module type Container_with_creators_tests = sig
    [%%template:
    [@@@alloc.default a = (heap, stack)]

    val test_container_s0_with_creators
      : ((module Container_s0_with_creators)[@alloc a]) test

    val test_container_s1_with_creators
      : ((module Container_s1_with_creators)[@alloc a]) test

    val test_container_generic_with_creators
      : ((module Container_generic_with_creators)[@alloc a]) test]
  end

  module type Indexed_container_with_creators_tests = sig
    [%%template:
    [@@@alloc.default a = (heap, stack)]

    val test_indexed_container_s0_with_creators
      : ((module Indexed_container_s0_with_creators)[@alloc a]) test

    val test_indexed_container_s1_with_creators
      : ((module Indexed_container_s1_with_creators)[@alloc a]) test

    val test_indexed_container_generic_with_creators
      : ((module Indexed_container_generic_with_creators)[@alloc a]) test]
  end
end

(** Top-level signature. *)

module type Base_container_tests = sig
  include module type of struct
    include Definitions
  end

  include Container_tests
  include Container_with_creators_tests
  include Indexed_container_tests
  include Indexed_container_with_creators_tests
end
