(*  Title:      Zippy/zippy_goals_tactic_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_COPY_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE

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
    structure Z : ZIPPY_BASE
    structure GOALS_TAC_COPY : ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
    sharing type GOALS_TAC_COPY.GCS.zipper = Z.Z1.zipper
    sharing type GOALS_TAC_COPY.GC.zipper = Z.Z2.zipper
    sharing type GOALS_TAC_COPY.COPY.zipper_from = Z.Z3.zipper
    sharing type GOALS_TAC_COPY.COPY.zipper_to = Z.Z1.zipper
    sharing type GOALS_TAC_COPY.M.t = Z.M.t
    sharing type GOALS_TAC_COPY.GCS.L.lens = Z.L.lens
  ) : ZIPPY_GOALS_TACTIC_COPY_MIXIN =
struct

open Z GOALS_TAC_COPY

local open SC MO A
in

fun gen_copy_cpos_focus move_cpos init_copy (cpos, focus) zipper =
  move_cpos cpos >>> init_copy focus zipper

local
  structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
    structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
    structure M = M)
in
fun gen_copy_cpos_focus_list copy_cpfocus cpfs x =
  LF.foldlM (fn cpf => AE.try (copy_cpfocus cpf x)) cpfs
end

fun gen_copy_update_focus copy_cpfocuss focus = (fn cud => copy_cpfocuss (cud focus)) |> COPY.copy
end

end

