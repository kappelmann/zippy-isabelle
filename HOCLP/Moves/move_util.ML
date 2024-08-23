(*  Title:      HOCLP/move_util.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_UTIL =
sig
  include MOVE_BASE
  structure AE : IARROW_EXCEPTION
  sharing type AE.cat = C.cat
  structure AC : IARROW_CHOICE_BASE
  sharing type AC.cat = C.cat
  structure SC : ISEMI_CATEGORY
  sharing type SC.cat = C.cat
  structure AF : IARROW_FOLD
  sharing type AF.AE.cat = C.cat
end

functor Move_Util(
    structure AE : IARROW_EXCEPTION
    structure AC : IARROW_CHOICE_BASE
    sharing type AC.cat = AE.cat
  ) : MOVE_UTIL =
struct

structure MB = Move_Base(AE)
open MB
structure AE = AE
structure AC = AC
structure SC = ISemi_Category(AE)
structure AF = IArrow_Fold(structure AE = AE; structure AC = AC)

end
