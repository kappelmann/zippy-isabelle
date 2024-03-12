(*  Title:      HOCLP/zipper_base.ML
    Author:     Kevin Kappelmann
*)
(*TODO: monadification and move somewhere else*)
(* structure Move_Result = Option_Monad_Trans(Identity_Monad) *)
(* structure Move_ResultMP = Option_Monad_Plus(Identity_Monad) *)
(* structure Move_Applicative  *)
(* structure Move = Kleisli_Arrow_Apply(Move_Result) *)
(* structure MoveA = Arrow(Move) *)
(* structure MoveAP = Kleisli_Arrow_Plus(Move_ResultMP) *)
(* structure State_Result = Pair_State_Result_Base *)
(* structure State_Move = State_Trans(structure M = Move_Result_Monad; structure SR = State_Result) *)
(* structure State_Move = IKleisli(State_Move) *)
signature ZIPPER_MOVE_BASE =
sig
  structure K : KLEISLI
  type ('a, 'b) move = ('a, 'b) K.kleisli
end

functor Zipper_Move_Base(K : KLEISLI) : ZIPPER_MOVE_BASE =
struct
  structure K = K
  type ('a, 'b) move = ('a, 'b) K.kleisli
end

signature ZIPPER_DIRECTION =
sig
  datatype direction = Init | Left | Right | Up | Down
end

structure Zipper_Direction : ZIPPER_DIRECTION =
struct
datatype direction = Init | Left | Right | Up | Down
end