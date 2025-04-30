(*  Title:      Zippy/zippy_ztactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ZTACTIC =
sig
  include ZIPPY_ZTACTIC_RESULT_UTIL
  structure RTAC : ZIPPY_RTACTIC

  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close>
  where type (@{ParaT_args} 'a) t = 'a Seq.seq
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close>
  where type (@{ParaT_args} 'a) K.M.t = 'a Seq.seq

  type 'm zippy_tactic = state -> 'm result Seq.seq (*equivalent to "(_, state, 'm result) A.cat"*)

  val all_tac : 'm -> 'm zippy_tactic

  val lift_single_goal_tac : (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) ->
    (int -> 'm RTAC.rtactic) -> GC.GCS.goal_pos -> 'm zippy_tactic

  val gen_lift_focus_tac : ((int -> 'm RTAC.rtactic) -> 'm zippy_tactic) ->
    ((int -> 'm RTAC.rtactic) -> GC.GCS.goal_pos list -> 'm zippy_tactic) ->
    (int -> 'm RTAC.rtactic) -> GPU.F.focus -> 'm zippy_tactic

  (*first parameter specifies how to combine consecutive more data*)
  val mTHEN : ('m * 'm -> 'm) -> 'm zippy_tactic * 'm zippy_tactic -> 'm zippy_tactic

  val mEVERY : 'm zippy_tactic -> ('m * 'm -> 'm) -> 'm zippy_tactic list -> 'm zippy_tactic
  val lift_every_goal_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm RTAC.rtactic) ->
    GC.GCS.goal_pos list -> 'm zippy_tactic
  val lift_every_focus_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm RTAC.rtactic) ->
    GPU.F.focus -> 'm zippy_tactic

  val ALLGOALS : 'm zippy_tactic -> ('m * 'm -> 'm) -> (GC.GCS.goal_pos -> 'm zippy_tactic) ->
    'm zippy_tactic
  val lift_all_goals_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm RTAC.rtactic) ->
    'm zippy_tactic
  val lift_all_goals_focus_tac : 'm zippy_tactic -> ('m * 'm -> 'm) ->
    (GPU.GCS.goal_pos -> int -> GPU.GCS.goal_pos GPU.T.target) -> (int -> 'm RTAC.rtactic) ->
    GPU.F.focus -> 'm zippy_tactic
end

functor Zippy_Tactic(
    structure R : ZIPPY_ZTACTIC_RESULT_UTIL
    structure RTAC : ZIPPY_RTACTIC
  ) : ZIPPY_ZTACTIC =
struct

open R
structure RTAC = RTAC

type 'm zippy_tactic = state -> 'm result Seq.seq

structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Seq_Monad_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
  open M A SC GPU
in
fun all_tac m state = pure (result m state GPU.id)

fun lift_single_goal_tac target_goal tac i state = tac i state
  >>= arr (fn {state = state', more} =>
    Zippy_Thm_State.nprems_of state' - Zippy_Thm_State.nprems_of state + 1
    |> single_goal_gpos_update target_goal i
    |> result more state')

fun gen_lift_focus_tac f_none _ tac F.None = f_none tac
  | gen_lift_focus_tac _ f_list tac (F.Goals is) = f_list tac is

fun mTHEN madd (tac1, tac2) =
  let
    fun tac2_update {state, more, gpos_update} =
      let
        val update_ud = map_gpos_update (General_Util.flip GPU.comp gpos_update)
        val update_m = map_more (curry madd more)
      in tac2 state >>= arr (update_ud #> update_m) end
  in tac1 >>> tac2_update end

(*invariant: position list is sorted*)
fun mEVERY empty_tac _ [] = empty_tac
  | mEVERY _ madd (tac :: tacs) = fold (curry (mTHEN madd)) tacs tac

fun lift_every_goal_tac empty_tac madd target_goal tac =
  List.map (lift_single_goal_tac target_goal tac) #> mEVERY empty_tac madd

fun lift_every_focus_tac empty_tac madd target_goal = gen_lift_focus_tac (K RTAC.no_tac)
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
