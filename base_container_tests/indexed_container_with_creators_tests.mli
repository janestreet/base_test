open! Base
open Base_container_tests_intf.Definitions

(** Functions for testing [Indexed_container.Generic_with_creators] and derived
    interfaces. *)
include Indexed_container_with_creators_tests

(** The back-end of [test_indexed_container_generic_with_creators]. Exported for testing
    extensions of [Indexed_container.Generic_with_creators].

    The [Container_with_creators_already_tested] and [Indexed_container_already_tested]
    arguments allows [Container.Generic_with_creators] and [Indexed_container.Generic] to
    be separately tested. The coverage can be shared with other tests, just as the two
    inputs should share their coverage for testing [Container.Generic]. *)
module%template
  [@alloc a @ l = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Indexed_container_generic_with_creators
  [@alloc a])
    (Container_with_creators_already_tested : Container.Generic_with_creators
                                              [@alloc a]
                                              with type 'a elt := 'a Impl.Elt.t
                                               and type ('a, 'p1, 'p2) t :=
                                                ('a, 'p1, 'p2) Impl.t
                                               and type ('a, 'p1, 'p2) concat :=
                                                ('a, 'p1, 'p2) Impl.concat)
    (Indexed_container_already_tested : Indexed_container.Generic
                                        [@alloc a]
                                        with type 'a elt := 'a Impl.Elt.t
                                         and type ('a, 'p1, 'p2) t :=
                                          ('a, 'p1, 'p2) Impl.t) :
  Indexed_container.Generic_with_creators
  [@alloc a]
  with type 'a elt := 'a Impl.Elt.t
   and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) Impl.t
   and type ('a, 'p1, 'p2) concat := ('a, 'p1, 'p2) Impl.concat
