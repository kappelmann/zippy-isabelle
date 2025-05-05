(*  Title:      Zippy/zippy_lists_gtcpp_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GTCPP_MIXIN =
sig
  include ZIPPY_GTCPP_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>

end

functor Zippy_Lists_GTCPP_Mixin(
    structure Z : ZIPPY_LISTS_BASE
    structure GTCPP : ZIPPY_GTCPP_MIXIN_BASE
    sharing type GTCPP.GCS.L.container = Z.Z1.zipper
    sharing type GTCPP.GC.L.container = Z.Z2.zipper
    sharing type GTCPP.COPY.zipper_to = Z.Z1.zipper
    sharing type GTCPP.PACTION.zipper = Z.Z4.zipper
    sharing type GTCPP.GCS.L.K.M.t = Z.M.t
    sharing type GTCPP.GCS.L.lens = Z.L.lens
    sharing type GTCPP.PRESULTS.CO.acoroutine = Z.CO.acoroutine
    sharing type GTCPP.PRESULTS.CO.AE.exn = Z.CO.AE.exn
  ) : ZIPPY_LISTS_GTCPP_MIXIN =
struct

open Z GTCPP
structure Base = struct structure Z = Z end
structure ZB = Zippy_Base(open Base; structure CO = CO); open ZB
(* structure ZGTC = Zippy_Goals_Tactic_Copy_Mixin(structure AE = AE; structure GOALS_TAC_COPY = GTCPP) *)
(* open ZGTC *)
structure ZLGT = Zippy_Lists_Goals_Tactic_Mixin(open Base; structure GOALS_TAC = GTCPP); open ZLGT
structure ZGT = Zippy_Goals_Tactic_Mixin(GTCPP); open ZGT
structure ZPP = Zippy_PAction_Presults_Mixin(structure Z = ZB; structure PACTION_PRESULTS = GTCPP)
open ZPP

local open SC MO
in
end

end

