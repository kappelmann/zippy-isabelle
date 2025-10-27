(*  Title:      Zippy/zippy_cresults_mixin_base.ML
    Author:     Kevin Kappelmann

Results with costs.
*)
signature ZIPPY_CRESULTS_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} cresults
  type @{AllT_args} zipper
  type cost
  type result
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t
  (*(cost, result) acoroutine*)
  val cresults : (@{ParaT_args} @{AllT_args} zipper, cost, result) Co.Co.acoroutine ->
    @{AllT_args} cresults
  val dest_cresults : @{AllT_args} cresults ->
    (@{ParaT_args} @{AllT_args} zipper, cost, result) Co.Co.acoroutine
  (*(cost * result sequence) coroutine*)
  type @{AllT_args} cresultsq =
    (*return next cost (estimate) while (optionally) updating the sequence*)
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, cost * result Seq.seq) Co.Co.coroutine
end

functor Zippy_CResults_Mixin_Base(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} cresults
    type @{AllT_args} zipper
    type cost
    type result
    structure Co : ZIPPY_COROUTINE_MIXIN_BASE
    sharing type Co.M.t = M.M.t
    val cresults : (@{ParaT_args} @{AllT_args} zipper, cost, result) Co.Co.acoroutine ->
      @{AllT_args} cresults
    val dest_cresults : @{AllT_args} cresults ->
      (@{ParaT_args} @{AllT_args} zipper, cost, result) Co.Co.acoroutine
  end
  ) : ZIPPY_CRESULTS_MIXIN_BASE
  =
struct
open A A.M
type @{AllT_args} cresultsq =
  (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, cost * result Seq.seq) Co.Co.coroutine
end
