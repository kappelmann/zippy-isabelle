(*  Title:      HOCLP/move_base.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_BASE =
sig
  structure M : MONAD_BASE
  include KLEISLI_ARROW_APPLY_BASE
  sharing type K.M.t = M.t
  type ('pi, 'a, 'b) move = ('pi, 'a, 'b) cat
  type ('pi, 'a) hom_move = ('pi, 'a, 'a) move
end

functor Move_Base(M : MONAD_BASE) : MOVE_BASE =
struct
  structure Min = M
  structure K = Kleisli_Arrow_Apply_Base(M)
  open K
  structure M = Min
  type ('pi, 'a, 'b) move = ('pi, 'a, 'b) cat
  type ('pi, 'a) hom_move = ('pi, 'a, 'a) move
end
