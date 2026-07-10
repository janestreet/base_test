open! Base
open Base_container_tests_intf.Definitions

(** Functions for testing [Indexed_container.Generic] and derived interfaces. *)
include Indexed_container_tests

(** The back-end of [test_indexed_container_generic]. Exported for testing extensions of
    [Indexed_container.Generic].

    The [Container_already_tested] argument allows [Container.Generic] to be separately
    tested using [Container_tests.Run], and the coverage may then be shared with this and
    other tests of signature extensions. *)
module%template
  [@alloc a @ l = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Indexed_container_generic
  [@alloc a])
    (Container_already_tested : Container.Generic
                                [@alloc a]
                                with type 'a elt := 'a Impl.Elt.t
                                 and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) Impl.t) :
  Indexed_container.Generic
  [@alloc a]
  with type 'a elt := 'a Impl.Elt.t
   and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) Impl.t
