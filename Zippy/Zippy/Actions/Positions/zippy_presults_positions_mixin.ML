(*  Title:      Zippy/zippy_presults_positions_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_POSITIONS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE
  val with_depth_prio_res_co : (int -> (@{ParaT_args} prio, prio) Co.C.cat) ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.coroutine ->
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.coroutine
end

functor Zippy_PResults_Positions_Mixin(
    structure Z : ZIPPY_POSITIONS_MIXIN
    structure PResults : ZIPPY_PRESULTS_MIXIN_BASE
    sharing type PResults.zipper = Z.Z4.zipper
  ) : ZIPPY_PRESULTS_POSITIONS_MIXIN
  =
struct
open Z PResults
structure MU = Zippy_Monad_Util(K.M); open MU

local open Mo A
in
fun with_depth_prio_res_co f co = (fn (z, sq) => Co.resume co (z, sq)
  >>= (first (f (ZZDepth_Co4.getter z)) *** arr (with_depth_prio_res_co f)))
  |> Co.coroutine
end

end