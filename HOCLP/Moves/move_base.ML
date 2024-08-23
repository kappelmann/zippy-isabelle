(*  Title:      HOCLP/move_base.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_BASE =
sig
  structure C : ICATEGORY_BASE
  type ('i, 'a, 'b) move = unit -> ('i, 'i, 'a, 'b) C.cat
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end

functor Move_Base(C : ICATEGORY_BASE) : MOVE_BASE =
struct
  structure C = C
  type ('i, 'a, 'b) move = unit -> ('i, 'i, 'a, 'b) C.cat
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end
