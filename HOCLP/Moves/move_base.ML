(*  Title:      HOCLP/move_base.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_BASE =
sig
  structure K : IKLEISLI
  type ('i, 'a) mt = ('i, 'i, 'a) K.M.t
  type ('i, 'a, 'b) move = ('i, 'i, 'a, 'b) K.kleisli
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end

functor Move_Base(K : IKLEISLI) : MOVE_BASE =
struct
  structure K = K
  type ('i, 'a) mt = ('i, 'i, 'a) K.M.t
  type ('i, 'a, 'b) move = ('i, 'i, 'a, 'b) K.kleisli
  type ('i, 'a) hom_move = ('i, 'a, 'a) move
end
