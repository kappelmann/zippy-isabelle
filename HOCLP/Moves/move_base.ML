(*  Title:      HOCLP/move_base.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_BASE =
sig
  include ICATEGORY_BASE
  type ('i, 'a, 'b) move = ('i, 'i, 'a, 'b) cat
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end

functor Move_Base(C : ICATEGORY_BASE) : MOVE_BASE =
struct
  open C
  type ('i, 'a, 'b) move = ('i, 'i, 'a, 'b) cat
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end
