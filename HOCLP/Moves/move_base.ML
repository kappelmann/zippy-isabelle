(*  Title:      HOCLP/move_base.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_BASE =
sig
  include CATEGORY_BASE
  type ('pi, 'a, 'b) move = ('pi, 'a, 'b) cat
  type ('pi, 'a) hom_move = ('pi, 'a, 'a) move
end

functor Move_Base(C : CATEGORY_BASE) : MOVE_BASE =
struct
  open C
  type ('pi, 'a, 'b) move = ('pi, 'a, 'b) cat
  type ('pi, 'a) hom_move = ('pi, 'a, 'a) move
end
