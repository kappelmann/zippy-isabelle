(*  Title:      HOCLP/zippy.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY =
sig
  include ZIPPY_PROVER_INSTANCE

  val cheat_tac : (thm * thm -> RMD.metadata) -> Proof.context -> F.focus ->
    RMD.metadata T.zippy_tactic
  val presults_from_cheat_tac : (thm * thm -> RMD.metadata) -> Proof.context -> P.prio -> F.focus ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} presults) cat
  val add_tac : (thm * thm -> RMD.metadata) -> Proof.context ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z4.zipper) cat
end

structure Zippy : ZIPPY =
struct

structure Z = Zippy_Prover_Instance(Zippy_Prover_Instance_Base(
  Monad_Exception_Monad_Or(Option_Monad_Or_Trans(Identity_Monad))))
open Z

fun halve_prio_co p = update_prio_co (fn _ => fn p => P.halve p) p

fun cheat_tac rdm ctxt x = x |>
  (resolve_tac ctxt [@{thm cheat}]
  |> T.lift_tac' rdm
  |> T.lift_all_goals_focus_tac T.no_tac fst T.single_goal_empty_target)
fun presults_from_cheat_tac rdm ctxt p f =
  presults_from_tac (halve_prio_co p) (cheat_tac rdm ctxt f)

local
  structure SC = Semi_Category(Z); structure M = Monad(K.M)
  open SC M
in

fun add_tac rdm ctxt x =
  ACMD.metadata (@{binding test}, "test cluster description")
  >>= mk_cd_more
  >>= (fn cdm => AMD.metadata (@{binding testaction}, "test action description")
  >>= mk_action_fd_more
  >>= (fn actionfdm => cons_move_single_presults_action' cdm actionfdm
    (presults_from_cheat_tac rdm ctxt P.MEDIUM) (Z.F.single 1) x))

end

end
