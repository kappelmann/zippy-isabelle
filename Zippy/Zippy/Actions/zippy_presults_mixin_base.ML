(*  Title:      Zippy/zippy_presults_mixin_base.ML
    Author:     Kevin Kappelmann

Prioritised results.
*)
signature ZIPPY_PRESULTS_MIXIN_BASE =
sig
  type @{AllT_args} presults
  type @{AllT_args} zipper

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = presults

  type prio
  type result
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) K.kleisli

  val presults : (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.acoroutine ->
    @{AllT_args} presults
  val dest_presults : @{AllT_args} presults ->
    (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.acoroutine
end

functor Zippy_PResults_Mixin_Base(A :
  sig
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
    type prio
    type result
    val presults : (@{ParaT_args} @{AllT_args} L.container, prio, result) Co.acoroutine ->
      @{AllT_args} L.data
    val dest_presults : @{AllT_args} L.data ->
      (@{ParaT_args} @{AllT_args} L.container, prio, result) Co.acoroutine
  end
  ) : ZIPPY_PRESULTS_MIXIN_BASE
  =
struct

open A
type @{AllT_args} zipper = @{AllT_args} L.container
type @{AllT_args} presults = @{AllT_args} L.data

end
