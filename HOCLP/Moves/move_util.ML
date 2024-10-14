(*  Title:      HOCLP/move_util.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_UTIL =
sig
  include MOVE_BASE
  structure AE : IARROW_EXCEPTION
  sharing type AE.cat = cat
  structure AC : IARROW_CHOICE
  sharing type AC.cat = cat
  structure SC : ISEMI_CATEGORY
  sharing type SC.cat = cat
  structure AF : IARROW_FOLD
  sharing type AF.AE.cat = cat
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
structure AC = IArrow_Choice(AC)
structure SC = ISemi_Category(AE)
structure AF = IArrow_Fold(structure AE = AE; structure AC = AC)

end
