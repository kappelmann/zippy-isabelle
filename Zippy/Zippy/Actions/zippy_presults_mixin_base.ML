(*  Title:      Zippy/zippy_presults_mixin_base.ML
    Author:     Kevin Kappelmann

Prioritised results.
*)
signature ZIPPY_PRESULTS_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} presults
  type @{AllT_args} zipper

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = presults

  type prio
  type result
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  val presults : (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.Co.acoroutine ->
    @{AllT_args} presults
  val dest_presults : @{AllT_args} presults ->
    (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.Co.acoroutine
end

functor Zippy_PResults_Mixin_Base(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = M.M.t
    type prio
    type result
    val presults : (@{ParaT_args} @{AllT_args} L.container, prio, result) Co.Co.acoroutine ->
      @{AllT_args} L.data
    val dest_presults : @{AllT_args} L.data ->
      (@{ParaT_args} @{AllT_args} L.container, prio, result) Co.Co.acoroutine
  end
  ) : ZIPPY_PRESULTS_MIXIN_BASE
  =
struct

open A A.M
type @{AllT_args} zipper = @{AllT_args} L.container
type @{AllT_args} presults = @{AllT_args} L.data

end
