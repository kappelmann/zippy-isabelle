(*  Title:      Zippy/zippy_cresults_positions_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_CRESULTS_POSITIONS_MIXIN =
sig
  include ZIPPY_CRESULTS_MIXIN_BASE

  val with_depth_cresultsq : (int -> (@{ParaT_args} cost) emorph) -> @{AllT_args} cresultsq ->
    @{AllT_args} cresultsq
end

functor Zippy_CResults_Positions_Mixin(
    structure Z : ZIPPY_POSITIONS_MIXIN
    structure CResults : ZIPPY_CRESULTS_MIXIN
    sharing type CResults.zipper = Z.Z4.zipper
  ) : ZIPPY_CRESULTS_POSITIONS_MIXIN
  =
struct
open Z CResults
structure MU = Zippy_Monad_Util(M); open MU

local open Mo A Co
in
fun with_depth_cresultsq f co = (fn (z, sq) => Co.resume co (z, sq)
  >>= (first (f (ZZDepth_Co4.getter z)) *** arr (with_depth_cresultsq f)))
  |> Co.coroutine
end

end