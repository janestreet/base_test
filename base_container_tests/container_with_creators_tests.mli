open! Base
open Base_container_tests_intf.Definitions

(** Functions for testing [Container.Generic_with_creators] and derived interfaces. *)
include Container_with_creators_tests

(** The back-end of [test_container_generic_with_creators]. Exported for testing
    extensions of [Container.Generic_with_creators].

    The [Container_already_tested] argument allows [Container.Generic] to be separately
    tested using [Container_tests.Run], and the coverage may then be shared with this and
    other tests of signature extensions. *)
module%template
  [@alloc a @ l = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Container_generic_with_creators
  [@alloc a])
    (Container_already_tested : Container.Generic
                                [@alloc a]
                                with type 'a elt := 'a Impl.Elt.t
                                 and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) Impl.t) :
  Container.Generic_with_creators
  [@alloc a]
  with type 'a elt := 'a Impl.Elt.t
   and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) Impl.t
   and type ('a, 'p1, 'p2) concat := ('a, 'p1, 'p2) Impl.concat
