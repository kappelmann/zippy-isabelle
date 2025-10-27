(*  Title:      Zippy/zippy_caction_mixin_base.ML
    Author:     Kevin Kappelmann

Actions with cost.
*)
signature ZIPPY_CACTION_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} caction
  type @{AllT_args} zipper
  type @{AllT_args} zipper_expanded
  type @{AllT_args} zipper_changed

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = caction

  structure AResult : ZIPPY_ACTION_RESULT

  type cost
  type @{AllT_args} action_result =
    (@{AllT_args} zipper, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed) AResult.result
  type @{AllT_args} action = cost -> (@{ParaT_args} @{AllT_args} zipper,
    @{AllT_args} action_result) morph

  val caction : (@{ParaT_args} @{AllT_args} zipper, cost * @{AllT_args} action) morph ->
    @{AllT_args} caction
  val run_caction : @{AllT_args} caction ->
    (@{ParaT_args} @{AllT_args} zipper, cost * @{AllT_args} action) morph
end

functor Zippy_CAction_Mixin_Base(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    type @{AllT_args} zipper_expanded
    type @{AllT_args} zipper_changed
    structure AResult : ZIPPY_ACTION_RESULT
    type cost
    val caction : (@{ParaT_args} @{AllT_args} L.container, cost *
        (cost -> (@{ParaT_args} @{AllT_args} L.container,
          (@{AllT_args} L.container, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed)
            AResult.result) M.morph)) M.morph ->
      @{AllT_args} L.data
    val run_caction : @{AllT_args} L.data -> (@{ParaT_args} @{AllT_args} L.container, cost *
      (cost -> (@{ParaT_args} @{AllT_args} L.container,
        (@{AllT_args} L.container, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed)
          AResult.result) M.morph)) M.morph
  end
  ) : ZIPPY_CACTION_MIXIN_BASE
  =
struct
open A A.M

type @{AllT_args} zipper = @{AllT_args} L.container
type @{AllT_args} caction = @{AllT_args} L.data
type @{AllT_args} action_result =
  (@{AllT_args} zipper, @{AllT_args} zipper_expanded, @{AllT_args} zipper_changed) AResult.result
type @{AllT_args} action = cost -> (@{ParaT_args} @{AllT_args} zipper,
  @{AllT_args} action_result) morph
end