(*  Title:      Zippy/zippy_ztactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ZTACTIC =
sig
  include ZIPPY_ZTACTIC_RESULT_UTIL
  structure RTac : ZIPPY_RTACTIC

  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close>
  where type (@{ParaT_args} 'a) t = 'a Seq.seq
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close>
  where type (@{ParaT_args} 'a) K.M.t = 'a Seq.seq

  type 'm ztactic = state -> 'm result Seq.seq (*equivalent to "(_, state, 'm result) A.cat"*)

  val no_tac : 'm ztactic
  val all_tac : 'm -> 'm ztactic

  val lift_rtac_single_goal : (int -> gpos_update) -> (int -> 'm RTac.rtactic) -> GC.GCS.goal_pos ->
    'm ztactic

  val gen_lift_rtac_focus : ((int -> 'm RTac.rtactic) -> 'm ztactic) -> ((int -> 'm RTac.rtactic) ->
    GC.GCS.goal_pos list -> 'm ztactic) -> (int -> 'm RTac.rtactic) -> GPU.F.focus -> 'm ztactic

  (*first parameter specifies how to combine consecutive more data*)
  val mTHEN : ('m * 'm -> 'm) -> 'm ztactic * 'm ztactic -> 'm ztactic

  val mEVERY : 'm ztactic -> ('m * 'm -> 'm) -> 'm ztactic list -> 'm ztactic
  val lift_rtac_every_goal : 'm ztactic -> ('m * 'm -> 'm) -> (int -> gpos_update) ->
    (int -> 'm RTac.rtactic) -> GC.GCS.goal_pos list -> 'm ztactic
  val lift_rtac_every_focus : 'm ztactic -> ('m * 'm -> 'm) -> (int -> gpos_update) ->
    (int -> 'm RTac.rtactic) -> GPU.F.focus -> 'm ztactic

  val ALLGOALS : 'm ztactic -> ('m * 'm -> 'm) -> (GC.GCS.goal_pos -> 'm ztactic) -> 'm ztactic
  val lift_rtac_all_goals : 'm ztactic -> ('m * 'm -> 'm) -> (int -> gpos_update) ->
    (int -> 'm RTac.rtactic) -> 'm ztactic
  val lift_rtac_all_focus : 'm ztactic -> ('m * 'm -> 'm) -> (int -> gpos_update) ->
    (int -> 'm RTac.rtactic) -> GPU.F.focus -> 'm ztactic
end

functor Zippy_ZTactic(
    structure R : ZIPPY_ZTACTIC_RESULT_UTIL
    structure RTac : ZIPPY_RTACTIC
  ) : ZIPPY_ZTACTIC =
struct

open R
structure RTac = RTac

type 'm ztactic = state -> 'm result Seq.seq

structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Seq_Monad_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
  open M A SC GPU
in
fun no_tac _ = Seq.empty
fun all_tac m state = pure (result m state GPU.id)

fun lift_rtac_single_goal update_goal tac i state = tac i state
  >>= arr (fn {state = state', more} =>
    Zippy_Thm_State.nprems_of state' - Zippy_Thm_State.nprems_of state + 1
    |> single_goal_gpos_update update_goal i
    |> result more state')

fun gen_lift_rtac_focus f_none _ tac F.None = f_none tac
  | gen_lift_rtac_focus _ f_list tac (F.Goals is) = f_list tac is

fun mTHEN madd (tac1, tac2) =
  let
    fun tac2_update {state, more, gpos_update} =
      let
        val update_ud = map_gpos_update (General_Util.flip GPU.comp gpos_update)
        val update_m = map_more (curry madd more)
      in tac2 state >>= arr (update_ud #> update_m) end
  in tac1 >>> tac2_update end

fun mEVERY empty_tac _ [] = empty_tac
  | mEVERY _ madd (tac :: tacs) = fold (curry (mTHEN madd)) tacs tac

(*invariant: position list is sorted*)
fun lift_rtac_every_goal empty_tac madd update_goal tac =
  List.map (lift_rtac_single_goal update_goal tac) #> mEVERY empty_tac madd

fun lift_rtac_every_focus empty_tac madd update_goal = gen_lift_rtac_focus (K no_tac)
  (lift_rtac_every_goal empty_tac madd update_goal)

fun ALLGOALS no_goals_tac madd tac st =
  let fun doall 0 = no_goals_tac
        | doall 1 = tac 1
        | doall n = mTHEN madd (tac n, doall (n - 1))
  in doall (Zippy_Thm_State.nprems_of st) st end

fun lift_rtac_all_goals no_goals_tac madd update_goal tac =
  ALLGOALS no_goals_tac madd (lift_rtac_single_goal update_goal tac)

fun lift_rtac_all_focus no_goals_tac madd update_goal = gen_lift_rtac_focus
  (lift_rtac_all_goals no_goals_tac madd update_goal)
  (lift_rtac_every_goal no_goals_tac madd update_goal)
end

end

structure Standard_Zippy_ZTactic = Zippy_ZTactic(
  structure R = Standard_Zippy_ZTactic_Result_Util
  structure RTac = Standard_Zippy_RTactic)
