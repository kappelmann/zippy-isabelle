(*  Title:      Zippy/zippy_presults_mixin_base.ML
    Author:     Kevin Kappelmann

Prioritised results.
*)
signature ZIPPY_PRESULTS_MIXIN_BASE =
sig
  type @{AllT_args} presults
  type @{AllT_args} zipper

  structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = presults

  type prio
  type result
  structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) L.C.cat

  val presults : (@{ParaT_args} @{AllT_args} zipper, prio, result) CO.acoroutine ->
    @{AllT_args} presults
  val dest_presults : @{AllT_args} presults ->
    (@{ParaT_args} @{AllT_args} zipper, prio, result) CO.acoroutine
end
