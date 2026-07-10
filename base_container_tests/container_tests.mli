open! Base
open Base_container_tests_intf.Definitions

(** Functions for testing [Container.Generic] and derived interfaces. *)
include Container_tests

(** The back-end of [test_container_generic]. Exported for testing extensions of
    [Container.Generic]. *)
module%template
  [@alloc a @ l = (heap_global, stack_local)] Run
    (Config : Helpers.Config)
    (Impl : Container_generic
  [@alloc a]) :
  Container.Generic
  [@alloc a]
  with type 'a elt := 'a Impl.Elt.t
   and type ('a, 'p1, 'p2) t := ('a, 'p1, 'p2) Impl.t
