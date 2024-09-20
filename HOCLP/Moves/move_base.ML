(*  Title:      HOCLP/move_base.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_BASE =
sig
  include LAZY_ICATEGORY_BASE
  type ('i, 'a, 'b) move = ('i, 'i, 'a, 'b) cat
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end

functor Move_Base(LC : LAZY_ICATEGORY_BASE) : MOVE_BASE =
struct
  open LC
  type ('i, 'a, 'b) move = ('i, 'i, 'a, 'b) cat
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end
