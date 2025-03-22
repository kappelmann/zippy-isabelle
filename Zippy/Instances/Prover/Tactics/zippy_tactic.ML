(*  Title:      Zippy/zippy_tactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC =
sig
  include ZIPPY_TACTIC_RESULT
  (*standard Isabelle tactic, equivalent to GC.GCS.state -> GC.GCS.state Seq.seq*)
  type tactic = Tactical.tactic
  (*generalised result tactic*)
  type 'm rtactic = GC.GCS.state -> 'm result_data Seq.seq
  (*Zippy tactic, including goal position update*)
  type 'm zippy_tactic = GC.GCS.state -> 'm result_update_data Seq.seq

  (*creates missing data from input and result state*)
  val lift_tac : (GC.GCS.state * GC.GCS.state -> 'm) -> tactic -> 'm rtactic
  val lift_tac' : (GC.GCS.state * GC.GCS.state -> 'm) -> ('a -> tactic) -> 'a -> 'm rtactic

  val no_tac : GC.GCS.state -> 'r Seq.seq
  val all_tac : 'm -> 'm zippy_tactic

  val lift_single_goal_tac : (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) ->
    (int -> 'm rtactic) -> GC.GCS.goal_pos -> 'm zippy_tactic

  val gen_lift_focus_tac : ((int -> 'm rtactic) -> 'm zippy_tactic) ->
    ((int -> 'm rtactic) -> GC.GCS.goal_pos list -> 'm zippy_tactic) ->
    (int -> 'm rtactic) -> GPU.F.focus -> 'm zippy_tactic

  val lift_single_focus_tac : (int -> 'm rtactic) -> GPU.F.focus -> 'm zippy_tactic

  val mTHEN : ('m * 'm -> 'm) -> 'm zippy_tactic * 'm zippy_tactic -> 'm zippy_tactic

  val mEVERY : 'm zippy_tactic -> ('m * 'm -> 'm) -> 'm zippy_tactic list -> 'm zippy_tactic
  val lift_every_goal_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm rtactic) ->
    GC.GCS.goal_pos list -> 'm zippy_tactic
  val lift_every_focus_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm rtactic) ->
    GPU.F.focus -> 'm zippy_tactic

  val ALLGOALS : 'm zippy_tactic -> ('m * 'm -> 'm) -> (GC.GCS.goal_pos -> 'm zippy_tactic) ->
    'm zippy_tactic
  val lift_all_goals_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm rtactic) ->
    'm zippy_tactic
  val lift_all_goals_focus_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm rtactic) ->
    GPU.F.focus -> 'm zippy_tactic
end

functor Zippy_Tactic(TR : ZIPPY_TACTIC_RESULT) : ZIPPY_TACTIC =
struct

structure SLens = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
structure SArrow_Arrow_Apply = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close>
open TR

type tactic = Tactical.tactic
type 'm rtactic = GC.GCS.state -> 'm result_data Seq.seq
type 'm zippy_tactic = GC.GCS.state -> 'm result_update_data Seq.seq

fun lift_tac f tac state = tac state
  |> Seq.map (fn state' => RD.result_data (state', f (state, state')))
fun lift_tac' f tac i = lift_tac f (tac i)

fun no_tac _ = Seq.empty

local
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Seq_Monad_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(M)
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
  open M A SC GPU
in

fun all_tac m state = pure (RUD.result_update_data (RD.result_data (state, m), GPU.id))

fun lift_single_goal_tac target_goal tac i state = tac i state
  >>= arr (fn rd =>
    let
      val state' = RD.get_result rd
      val ud =  Zippy_Thm_State.nprems_of state' - Zippy_Thm_State.nprems_of state
        |> single_goal_update_data target_goal i
    in RUD.result_update_data (rd, ud) end)

fun gen_lift_focus_tac f_none _ tac F.None = f_none tac
  | gen_lift_focus_tac _ f_list tac (F.Goals is) = f_list tac is

fun lift_single_focus_tac x = gen_lift_focus_tac (K no_tac) (K (K no_tac)) x

fun mTHEN madd (tac1, tac2) =
  let
    fun tac2_update rud =
      let
        val (state, m) = RUD.get_result rud |> SArrow_Arrow_Apply.A.&&& (RD.get_result, RD.get_more)
        val ud = RUD.get_update_data rud
        fun gen_update modifier add x = curry modifier (fn x' => add x' x)
        val update_ud = gen_update RUD.map_update_data GPU.comp ud
        val update_m = gen_update (RUD.map_result |> SLens.comp_modify RD.map_more) (curry madd) m
      in tac2 state >>= arr (update_ud #> update_m) end
  in tac1 >>> tac2_update end

(*invariant: position list is sorted*)
fun mEVERY empty_tac _ [] = empty_tac
  | mEVERY _ madd (tac :: tacs) = fold (curry (mTHEN madd)) tacs tac
fun lift_every_goal_tac empty_tac madd target_goal tac =
  List.map (lift_single_goal_tac target_goal tac) #> mEVERY empty_tac madd
fun lift_every_focus_tac empty_tac madd target_goal = gen_lift_focus_tac (K no_tac)
  (lift_every_goal_tac empty_tac madd target_goal)

fun ALLGOALS no_goals_tac madd tac st =
  let fun doall 0 = no_goals_tac
        | doall 1 = tac 1
        | doall n = mTHEN madd (tac n, doall (n - 1))
  in doall (Zippy_Thm_State.nprems_of st) st end
fun lift_all_goals_tac no_goals_tac madd target_goal tac =
  ALLGOALS no_goals_tac madd (lift_single_goal_tac target_goal tac)
fun lift_all_goals_focus_tac no_goals_tac madd target_goal = gen_lift_focus_tac
  (lift_all_goals_tac no_goals_tac madd target_goal)
  (lift_every_goal_tac no_goals_tac madd target_goal)

end

end
