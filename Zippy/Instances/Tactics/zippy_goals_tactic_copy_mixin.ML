(*  Title:      Zippy/zippy_goals_tactic_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_COPY_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

  val gen_copy_cpos_focus :
    (*move to cluster position*)
    (GCS.GCS.cluster_pos -> (@{ParaT_args} 'z1, 'z2) cat) ->
    (*initialise the copy*)
    (TAC.GPU.F.focus -> 'z3 -> (@{ParaT_args} 'z2, 'z4) cat) ->
    (GCS.GCS.cluster_pos * TAC.GPU.F.focus) -> 'z3 -> (@{ParaT_args} 'z1, 'z4) cat

  val gen_copy_cpos_focus_list :
    (GCS.GCS.cluster_pos * TAC.GPU.F.focus -> 'z3 -> (@{ParaT_args} 'z1) hom_move) ->
    (GCS.GCS.cluster_pos * TAC.GPU.F.focus) list -> 'z3 -> (@{ParaT_args} 'z1) hom_move

  val gen_copy_update_focus :
    ((GCS.GCS.cluster_pos * TAC.GPU.F.focus) list -> @{AllT_args} COPY.zipper_from ->
      (@{ParaT_args} @{AllT_args} COPY.zipper_to) hom_move) ->
    TAC.GPU.F.focus -> @{AllT_args} COPY.copy
end

functor Zippy_Goals_Tactic_Copy_Mixin(
    structure GOALS_TAC_COPY : ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
    sharing type AE.K.M.t = GOALS_TAC_COPY.GCS.L.K.M.t
  ) : ZIPPY_GOALS_TACTIC_COPY_MIXIN =
struct

open GOALS_TAC_COPY
structure MB = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(GCS.L.K.M); open MB

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(MB); open SC
in

fun gen_copy_cpos_focus move_cpos init_copy (cpos, focus) zipper =
  move_cpos cpos >>> init_copy focus zipper

local
  structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
    structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
    structure M = M)
in
fun gen_copy_cpos_focus_list copy_cpos_focus cpfs x =
  LF.foldlM (fn cpf => AE.try (copy_cpos_focus cpf x)) cpfs
end

fun gen_copy_update_focus copy_cpos_focuss focus =
  (fn cud => copy_cpos_focuss (cud focus)) |> COPY.copy
end

end

