(*  Title:      Zippy/zippy_presults_positions_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PRESULTS_POSITIONS_MIXIN =
sig
  include ZIPPY_PRESULTS_MIXIN_BASE

  type @{AllT_args} prio_sq_co =
    (@{ParaT_args} @{AllT_args} zipper * result Seq.seq, prio * result Seq.seq) Co.Co.coroutine

  val with_depth_prio_sq_co : (int -> (@{ParaT_args} prio) emorph) -> @{AllT_args} prio_sq_co ->
    @{AllT_args} prio_sq_co
end

functor Zippy_PResults_Positions_Mixin(
    structure Z : ZIPPY_POSITIONS_MIXIN
    structure PResults : ZIPPY_PRESULTS_MIXIN
    sharing type PResults.zipper = Z.Z4.zipper
  ) : ZIPPY_PRESULTS_POSITIONS_MIXIN
  =
struct
open Z PResults
structure MU = Zippy_Monad_Util(M); open MU

local open Mo A Co
in
fun with_depth_prio_sq_co f co = (fn (z, sq) => Co.resume co (z, sq)
  >>= (first (f (ZZDepth_Co4.getter z)) *** arr (with_depth_prio_sq_co f)))
  |> Co.coroutine
end

end