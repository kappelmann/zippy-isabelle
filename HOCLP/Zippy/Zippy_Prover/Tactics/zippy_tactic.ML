(*  Title:      HOCLP/zippy_tactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC =
sig
  include ZIPPY_TACTIC_RESULT
  type zippy_tactic = GC.GCS.state -> result_update_data Seq.seq
  val no_tac : zippy_tactic
  val all_tac : zippy_tactic

  val lift_single_goal_tac : (int -> tactic) -> GC.GCS.goal_pos -> zippy_tactic

  val gen_lift_focus_tac : ((int -> tactic) -> zippy_tactic) ->
    ((int -> tactic) -> GC.GCS.goal_pos list -> zippy_tactic) ->
    (int -> tactic) -> GPU.F.focus -> zippy_tactic

  val lift_single_focus_tac : (int -> tactic) -> GPU.F.focus -> zippy_tactic

  val THEN : zippy_tactic * zippy_tactic -> zippy_tactic

  val EVERY : zippy_tactic list -> zippy_tactic
  val lift_every_goal_tac : (int -> tactic) -> GC.GCS.goal_pos list -> zippy_tactic
  val lift_every_focus_tac : (int -> tactic) -> GPU.F.focus -> zippy_tactic

  val ALLGOALS : (GC.GCS.goal_pos -> zippy_tactic) -> zippy_tactic
  val lift_all_goals_tac : (int -> tactic) -> zippy_tactic
  val lift_all_goals_focus_tac : (int -> tactic) -> GPU.F.focus -> zippy_tactic
end

functor Zippy_Tactic(TR : ZIPPY_TACTIC_RESULT) : ZIPPY_TACTIC =
struct

open TR

type zippy_tactic = GC.GCS.state -> result_update_data Seq.seq

fun lift_single_goal_tac tac i state = tac i state
  |> Seq.map (fn state' => Zippy_Thm_State.nprems_of state' - Zippy_Thm_State.nprems_of state
    |> mk_single_goal_update_data i
    |> curry RUD.result_update_data state')

local open GPU
in

val no_tac = K Seq.empty
fun all_tac state = Seq.single (RUD.result_update_data (state, GPU.id))

fun gen_lift_focus_tac f_none _ tac F.None = f_none tac
  | gen_lift_focus_tac _ _ tac (F.Single i) = lift_single_goal_tac tac i
  | gen_lift_focus_tac _ f_list tac (F.List is) = f_list tac is

val lift_single_focus_tac = gen_lift_focus_tac (K no_tac) (K (K no_tac))

fun (tac1 THEN tac2) state =
  let fun next rud =
    let
      val state = RUD.get_result rud
      val ud = RUD.get_update_data rud
      val update_ud = curry RUD.map_update_data (fn ud' => GPU.comp ud' ud)
    in Seq.map update_ud (tac2 state) end
  in Seq.maps next (tac1 state) end

(*invariant: position list is sorted*)
fun EVERY tacs = fold (curry (op THEN)) tacs all_tac
fun lift_every_goal_tac tac is = map (lift_single_goal_tac tac) is |> EVERY
val lift_every_focus_tac = gen_lift_focus_tac (K no_tac) lift_every_goal_tac

fun ALLGOALS tac st =
  let fun doall 0 = all_tac
        | doall n = tac n THEN doall (n - 1)
  in doall (Zippy_Thm_State.nprems_of st) st end
val lift_all_goals_tac = ALLGOALS o lift_single_goal_tac
val lift_all_goals_focus_tac = gen_lift_focus_tac lift_all_goals_tac lift_every_goal_tac

end

end
